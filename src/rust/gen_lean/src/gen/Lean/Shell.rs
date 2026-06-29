// Lean compiler output
// Module: Lean.Shell
// Imports: Lean.Elab.Frontend Lean.Elab.ParseImportsFast Lean.Server.Watchdog Lean.Server.FileWorker Lean.Compiler.LCNF.EmitRust Init.System.Platform Lean.Compiler.Options
use crate::ffi::{
    lean_array_mk, lean_array_push, lean_array_to_list, lean_decode_lossy_utf8,
    lean_display_cumulative_profiling_times, lean_emit_llvm, lean_eval_main, lean_get_stderr,
    lean_get_stdin, lean_get_stdout, lean_init_llvm, lean_internal_enable_debug,
    lean_internal_get_believer_trust_level, lean_internal_get_build_type,
    lean_internal_get_default_max_heartbeat, lean_internal_get_default_max_memory,
    lean_internal_get_default_options, lean_internal_get_default_verbose,
    lean_internal_get_hardware_concurrency, lean_internal_has_address_sanitizer,
    lean_internal_has_llvm_backend, lean_internal_is_debug, lean_internal_is_multi_thread,
    lean_internal_set_exit_on_panic, lean_internal_set_max_heartbeat, lean_internal_set_max_memory,
    lean_internal_set_thread_stack_size, lean_io_exit, lean_io_get_num_heartbeats,
    lean_io_prim_handle_mk, lean_io_prim_handle_write, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_pow,
    lean_nat_shiftr, lean_nat_sub, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_append, lean_string_dec_eq, lean_string_memcmp, lean_string_push,
    lean_string_to_utf8, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_add, lean_uint32_dec_eq,
    lean_uint32_of_nat, lean_usize_mul, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Slice::{
    l_String_Slice_beq, l_String_Slice_toName, l_String_Slice_toNat_x3f, l_String_Slice_toString,
    l_String_Slice_trimAscii,
};
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringString___lam__0___boxed;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_githash, l_Lean_version_isRelease, l_Lean_version_specialDesc, l_Lean_versionStringCore,
    l_String_toName,
};
use crate::r#gen::Init::Prelude::{l_Lean_firstFrontendMacroScope, l_System_Platform_numBits};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_Stream_lines, l_IO_FS_Stream_putStrLn, l_IO_FS_Stream_readBinToEnd,
    l_IO_FS_readBinFile, l_IO_eprint___redArg,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_target,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Lean::Compiler::LCNF::EmitRust::{
    initialize_Lean_Compiler_LCNF_EmitRust, l_Lean_Compiler_LCNF_emitRust,
    runtime_initialize_Lean_Compiler_LCNF_EmitRust,
};
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_postponeCompile,
    runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Core_getMaxHeartbeats, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::{
    l_Lean_Options_empty, l_Lean_getOptionDecls, lean_register_option,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Elab::Frontend::{
    initialize_Lean_Elab_Frontend, l_Lean_Elab_runFrontend, runtime_initialize_Lean_Elab_Frontend,
};
use crate::r#gen::Lean::Elab::Import::{l_Lean_Elab_printImportSrcs, l_Lean_Elab_printImports};
use crate::r#gen::Lean::Elab::ParseImportsFast::{
    initialize_Lean_Elab_ParseImportsFast, l_Lean_printImportsJson,
    runtime_initialize_Lean_Elab_ParseImportsFast,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Language::Lean::l_Lean_Language_Lean_setOption;
use crate::r#gen::Lean::Message::l_Lean_MessageData_toString;
use crate::r#gen::Lean::Server::FileWorker::{
    initialize_Lean_Server_FileWorker, l_Lean_Server_FileWorker_workerMain,
    runtime_initialize_Lean_Server_FileWorker,
};
use crate::r#gen::Lean::Server::Watchdog::{
    initialize_Lean_Server_Watchdog, l_Lean_Server_Watchdog_watchdogMain,
    runtime_initialize_Lean_Server_Watchdog,
};
use crate::r#gen::Lean::Setup::l_Lean_ModuleSetup_load;
use crate::r#gen::Lean::Util::Path::{
    l_Lean_getBuildDir, l_Lean_getLibDir, l_Lean_moduleNameOfFileName,
};
use crate::r#gen::Lean::Util::Profile::{l_Lean_profileitIOUnsafe___redArg, l_Lean_profiler};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::l_Lean_inheritedTraceOptions;
pub static l___private_Lean_Shell_0__Lean_shortVersionString___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__1: u8 = 0;
pub static l___private_Lean_Shell_0__Lean_shortVersionString___closed__2_value:
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
    m_data: [45, 0],
};
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_value:
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
    m_data: [45, 112, 114, 101, 0],
};
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_shortVersionString___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Shell_0__Lean_shortVersionString: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_versionHeader___closed__0_value:
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
        76, 101, 97, 110, 32, 40, 118, 101, 114, 115, 105, 111, 110, 32, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_versionHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_versionHeader___closed__1_value:
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
    m_data: [44, 32, 0],
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_versionHeader___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_versionHeader___closed__3_value:
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
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_versionHeader___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__4: u8 = 0;
pub static l___private_Lean_Shell_0__Lean_versionHeader___closed__5_value:
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
    m_data: [44, 32, 99, 111, 109, 109, 105, 116, 32, 0],
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_versionHeader___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__6: u8 = 0;
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_versionHeader___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Shell_0__Lean_versionHeader: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_featuresString___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_featuresString___closed__0: u8 = 0;
pub static l___private_Lean_Shell_0__Lean_featuresString___closed__1_value:
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
    m_data: [91, 93, 0],
};
static mut l___private_Lean_Shell_0__Lean_featuresString___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_featuresString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_featuresString___closed__2_value:
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
    m_data: [91, 76, 76, 86, 77, 93, 0],
};
static mut l___private_Lean_Shell_0__Lean_featuresString___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_featuresString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Shell_0__Lean_featuresString: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__0_value:
    crate::leanh::LeanStringObject<77> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 77,
    m_capacity: 77,
    m_length: 76,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 68, 32, 110, 97, 109, 101, 61, 118, 97, 108, 117, 101, 32, 32,
        32, 32, 32, 32, 115, 101, 116, 32, 97, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116,
        105, 111, 110, 32, 111, 112, 116, 105, 111, 110, 32, 40, 115, 101, 101, 32, 115, 101, 116,
        95, 111, 112, 116, 105, 111, 110, 32, 99, 111, 109, 109, 97, 110, 100, 41, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__1_value:
    crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 112, 108, 117, 103, 105, 110, 61, 102, 105, 108, 101, 91,
        61, 102, 110, 93, 32, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 105, 110,
        32, 116, 104, 101, 32, 82, 117, 115, 116, 47, 67, 97, 114, 103, 111, 32, 98, 97, 99, 107,
        101, 110, 100, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__2_value:
    crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 108, 111, 97, 100, 45, 100, 121, 110, 108, 105, 98, 61,
        102, 105, 108, 101, 32, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 105,
        110, 32, 116, 104, 101, 32, 82, 117, 115, 116, 47, 67, 97, 114, 103, 111, 32, 98, 97, 99,
        107, 101, 110, 100, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__3_value:
    crate::leanh::LeanStringObject<89> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 89,
    m_capacity: 89,
    m_length: 88,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 115, 101, 116, 117, 112, 61, 102, 105, 108, 101, 32, 32,
        32, 32, 32, 32, 32, 74, 83, 79, 78, 32, 102, 105, 108, 101, 32, 119, 105, 116, 104, 32,
        109, 111, 100, 117, 108, 101, 32, 115, 101, 116, 117, 112, 32, 100, 97, 116, 97, 32, 40,
        115, 117, 112, 101, 114, 115, 101, 100, 101, 115, 32, 116, 104, 101, 32, 102, 105, 108,
        101, 39, 115, 32, 104, 101, 97, 100, 101, 114, 41, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__4_value:
    crate::leanh::LeanStringObject<84> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 84,
    m_capacity: 84,
    m_length: 83,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 106, 115, 111, 110, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 114, 101, 112, 111, 114, 116, 32, 76, 101, 97, 110, 32, 111, 117, 116, 112,
        117, 116, 32, 40, 101, 46, 103, 46, 44, 32, 109, 101, 115, 115, 97, 103, 101, 115, 41, 32,
        97, 115, 32, 74, 83, 79, 78, 32, 40, 111, 110, 101, 32, 112, 101, 114, 32, 108, 105, 110,
        101, 41, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__5_value:
    crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 64,
    m_capacity: 64,
    m_length: 63,
    m_data: [
        32, 32, 45, 69, 44, 32, 45, 45, 101, 114, 114, 111, 114, 61, 107, 105, 110, 100, 32, 32,
        32, 32, 32, 32, 32, 114, 101, 112, 111, 114, 116, 32, 76, 101, 97, 110, 32, 109, 101, 115,
        115, 97, 103, 101, 115, 32, 111, 102, 32, 107, 105, 110, 100, 32, 97, 115, 32, 101, 114,
        114, 111, 114, 115, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__6_value:
    crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 65,
    m_capacity: 65,
    m_length: 64,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 100, 101, 112, 115, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 106, 117, 115, 116, 32, 112, 114, 105, 110, 116, 32, 100, 101, 112, 101, 110,
        100, 101, 110, 99, 105, 101, 115, 32, 111, 102, 32, 97, 32, 76, 101, 97, 110, 32, 105, 110,
        112, 117, 116, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__7_value:
    crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 71,
    m_capacity: 71,
    m_length: 70,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 115, 114, 99, 45, 100, 101, 112, 115, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 106, 117, 115, 116, 32, 112, 114, 105, 110, 116, 32, 100, 101, 112, 101,
        110, 100, 101, 110, 99, 121, 32, 115, 111, 117, 114, 99, 101, 115, 32, 111, 102, 32, 97,
        32, 76, 101, 97, 110, 32, 105, 110, 112, 117, 116, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__8_value:
    crate::leanh::LeanStringObject<73> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 73,
    m_capacity: 73,
    m_length: 72,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 112, 114, 105, 110, 116, 45, 112, 114, 101, 102, 105, 120,
        32, 32, 32, 32, 32, 112, 114, 105, 110, 116, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97,
        108, 108, 97, 116, 105, 111, 110, 32, 112, 114, 101, 102, 105, 120, 32, 102, 111, 114, 32,
        76, 101, 97, 110, 32, 97, 110, 100, 32, 101, 120, 105, 116, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__9_value:
    crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 97,
    m_capacity: 97,
    m_length: 96,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 112, 114, 105, 110, 116, 45, 108, 105, 98, 100, 105, 114,
        32, 32, 32, 32, 32, 112, 114, 105, 110, 116, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97,
        108, 108, 97, 116, 105, 111, 110, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 102,
        111, 114, 32, 76, 101, 97, 110, 39, 115, 32, 98, 117, 105, 108, 116, 45, 105, 110, 32, 108,
        105, 98, 114, 97, 114, 105, 101, 115, 32, 97, 110, 100, 32, 101, 120, 105, 116, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__10_value:
    crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 92,
    m_capacity: 92,
    m_length: 91,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 112, 114, 111, 102, 105, 108, 101, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 100, 105, 115, 112, 108, 97, 121, 32, 101, 108, 97, 98, 111, 114, 97, 116,
        105, 111, 110, 47, 116, 121, 112, 101, 32, 99, 104, 101, 99, 107, 105, 110, 103, 32, 116,
        105, 109, 101, 32, 102, 111, 114, 32, 101, 97, 99, 104, 32, 100, 101, 102, 105, 110, 105,
        116, 105, 111, 110, 47, 116, 104, 101, 111, 114, 101, 109, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__11_value:
    crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 56,
    m_capacity: 56,
    m_length: 55,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 115, 116, 97, 116, 115, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 100, 105, 115, 112, 108, 97, 121, 32, 101, 110, 118, 105, 114, 111, 110, 109,
        101, 110, 116, 32, 115, 116, 97, 116, 105, 115, 116, 105, 99, 115, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__12: u8 = 0;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__13_value:
    crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 100, 101, 98, 117, 103, 61, 116, 97, 103, 32, 32, 32, 32,
        32, 32, 32, 32, 101, 110, 97, 98, 108, 101, 32, 97, 115, 115, 101, 114, 116, 105, 111, 110,
        115, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 116, 97,
        103, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__14_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        77, 105, 115, 99, 101, 108, 108, 97, 110, 101, 111, 117, 115, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__15_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        32, 32, 45, 104, 44, 32, 45, 45, 104, 101, 108, 112, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 104, 105, 115, 32, 109, 101,
        115, 115, 97, 103, 101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__16_value:
    crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 79,
    m_capacity: 79,
    m_length: 78,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 102, 101, 97, 116, 117, 114, 101, 115, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 100, 105, 115, 112, 108, 97, 121, 32, 102, 101, 97, 116, 117, 114, 101,
        115, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 112, 114, 111, 118, 105, 100, 101, 115,
        32, 40, 101, 103, 46, 32, 76, 76, 86, 77, 32, 115, 117, 112, 112, 111, 114, 116, 41, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__17_value:
    crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        32, 32, 45, 118, 44, 32, 45, 45, 118, 101, 114, 115, 105, 111, 110, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 100, 105, 115, 112, 108, 97, 121, 32, 118, 101, 114, 115, 105, 111, 110,
        32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__18_value:
    crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        32, 32, 45, 86, 44, 32, 45, 45, 115, 104, 111, 114, 116, 45, 118, 101, 114, 115, 105, 111,
        110, 32, 32, 32, 32, 100, 105, 115, 112, 108, 97, 121, 32, 115, 104, 111, 114, 116, 32,
        118, 101, 114, 115, 105, 111, 110, 32, 110, 117, 109, 98, 101, 114, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__19_value:
    crate::leanh::LeanStringObject<86> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 86,
    m_capacity: 86,
    m_length: 85,
    m_data: [
        32, 32, 45, 103, 44, 32, 45, 45, 103, 105, 116, 104, 97, 115, 104, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 104, 101, 32, 103, 105, 116, 32,
        99, 111, 109, 109, 105, 116, 32, 104, 97, 115, 104, 32, 110, 117, 109, 98, 101, 114, 32,
        117, 115, 101, 100, 32, 116, 111, 32, 98, 117, 105, 108, 100, 32, 116, 104, 105, 115, 32,
        98, 105, 110, 97, 114, 121, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__20_value:
    crate::leanh::LeanStringObject<99> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 99,
    m_capacity: 99,
    m_length: 98,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 114, 117, 110, 32, 60, 102, 105, 108, 101, 62, 32, 32, 32,
        32, 32, 32, 32, 99, 97, 108, 108, 32, 116, 104, 101, 32, 39, 109, 97, 105, 110, 39, 32,
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 103,
        105, 118, 101, 110, 32, 102, 105, 108, 101, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32,
        114, 101, 109, 97, 105, 110, 105, 110, 103, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115,
        0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__21_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        32, 32, 45, 111, 44, 32, 45, 45, 111, 61, 111, 110, 97, 109, 101, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 99, 114, 101, 97, 116, 101, 32, 111, 108, 101, 97, 110, 32, 102, 105, 108,
        101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__22_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        32, 32, 45, 105, 44, 32, 45, 45, 105, 61, 105, 110, 97, 109, 101, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 99, 114, 101, 97, 116, 101, 32, 105, 108, 101, 97, 110, 32, 102, 105, 108,
        101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__23_value:
    crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        32, 32, 45, 99, 44, 32, 45, 45, 114, 117, 115, 116, 61, 102, 110, 97, 109, 101, 32, 32, 32,
        32, 32, 32, 32, 110, 97, 109, 101, 32, 111, 102, 32, 116, 104, 101, 32, 82, 117, 115, 116,
        32, 111, 117, 116, 112, 117, 116, 32, 102, 105, 108, 101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__24_value:
    crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        32, 32, 45, 98, 44, 32, 45, 45, 98, 99, 61, 102, 110, 97, 109, 101, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 110, 97, 109, 101, 32, 111, 102, 32, 116, 104, 101, 32, 76, 76, 86, 77, 32, 98,
        105, 116, 99, 111, 100, 101, 32, 102, 105, 108, 101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__25_value:
    crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 115, 116, 100, 105, 110, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 116, 97, 107, 101, 32, 105, 110, 112, 117, 116, 32, 102, 114, 111, 109, 32,
        115, 116, 100, 105, 110, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__26_value:
    crate::leanh::LeanStringObject<80> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 80,
    m_capacity: 80,
    m_length: 79,
    m_data: [
        32, 32, 45, 82, 44, 32, 45, 45, 114, 111, 111, 116, 61, 100, 105, 114, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 115, 101, 116, 32, 112, 97, 99, 107, 97, 103, 101, 32, 114, 111, 111, 116,
        32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 102, 114, 111, 109, 32, 119, 104, 105,
        99, 104, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 110, 97, 109, 101, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__27_value:
    crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 112, 117, 116, 32, 102, 105, 108, 101,
        32, 105, 115, 32, 99, 97, 108, 99, 117, 108, 97, 116, 101, 100, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__28_value:
    crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 40, 100, 101, 102, 97, 117, 108, 116, 58, 32, 99, 117, 114, 114, 101, 110, 116, 32,
        119, 111, 114, 107, 105, 110, 103, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 41, 10,
        0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__29_value:
    crate::leanh::LeanStringObject<85> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 85,
    m_capacity: 85,
    m_length: 84,
    m_data: [
        32, 32, 45, 116, 44, 32, 45, 45, 116, 114, 117, 115, 116, 61, 110, 117, 109, 32, 32, 32,
        32, 32, 32, 32, 32, 116, 114, 117, 115, 116, 32, 108, 101, 118, 101, 108, 32, 40, 100, 101,
        102, 97, 117, 108, 116, 58, 32, 109, 97, 120, 41, 32, 48, 32, 109, 101, 97, 110, 115, 32,
        100, 111, 32, 110, 111, 116, 32, 116, 114, 117, 115, 116, 32, 97, 110, 121, 32, 109, 97,
        99, 114, 111, 44, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__30_value:
    crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 97, 110, 100, 32, 116, 121, 112, 101, 32, 99, 104, 101, 99, 107, 32, 97, 108, 108,
        32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 115, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__31_value:
    crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        32, 32, 45, 113, 44, 32, 45, 45, 113, 117, 105, 101, 116, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 100, 111, 32, 110, 111, 116, 32, 112, 114, 105, 110, 116, 32, 118, 101,
        114, 98, 111, 115, 101, 32, 109, 101, 115, 115, 97, 103, 101, 115, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__32_value:
    crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 78,
    m_capacity: 78,
    m_length: 77,
    m_data: [
        32, 32, 45, 77, 44, 32, 45, 45, 109, 101, 109, 111, 114, 121, 61, 110, 117, 109, 32, 32,
        32, 32, 32, 32, 32, 109, 97, 120, 105, 109, 117, 109, 32, 97, 109, 111, 117, 110, 116, 32,
        111, 102, 32, 109, 101, 109, 111, 114, 121, 32, 116, 104, 97, 116, 32, 115, 104, 111, 117,
        108, 100, 32, 98, 101, 32, 117, 115, 101, 100, 32, 98, 121, 32, 76, 101, 97, 110, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__33_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 40, 105, 110, 32, 109, 101, 103, 97, 98, 121, 116, 101, 115, 41, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__34_value:
    crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 71,
    m_capacity: 71,
    m_length: 70,
    m_data: [
        32, 32, 45, 84, 44, 32, 45, 45, 116, 105, 109, 101, 111, 117, 116, 61, 110, 117, 109, 32,
        32, 32, 32, 32, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32,
        111, 102, 32, 109, 101, 109, 111, 114, 121, 32, 97, 108, 108, 111, 99, 97, 116, 105, 111,
        110, 115, 32, 112, 101, 114, 32, 116, 97, 115, 107, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__35_value:
    crate::leanh::LeanStringObject<88> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 88,
    m_capacity: 88,
    m_length: 87,
    m_data: [
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 116, 104, 105, 115, 32, 105, 115, 32, 97, 32, 100, 101, 116, 101, 114, 109, 105,
        110, 105, 115, 116, 105, 99, 32, 119, 97, 121, 32, 111, 102, 32, 105, 110, 116, 101, 114,
        114, 117, 112, 116, 105, 110, 103, 32, 108, 111, 110, 103, 32, 114, 117, 110, 110, 105,
        110, 103, 32, 116, 97, 115, 107, 115, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__35_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__36: u8 = 0;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__37_value:
    crate::leanh::LeanStringObject<70> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 70,
    m_capacity: 70,
    m_length: 69,
    m_data: [
        32, 32, 45, 106, 44, 32, 45, 45, 116, 104, 114, 101, 97, 100, 115, 61, 110, 117, 109, 32,
        32, 32, 32, 32, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 116, 104, 114, 101, 97,
        100, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 112, 114, 111, 99, 101, 115, 115, 32,
        108, 101, 97, 110, 32, 102, 105, 108, 101, 115, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__38_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        32, 32, 45, 115, 44, 32, 45, 45, 116, 115, 116, 97, 99, 107, 61, 110, 117, 109, 32, 32, 32,
        32, 32, 32, 32, 116, 104, 114, 101, 97, 100, 32, 115, 116, 97, 99, 107, 32, 115, 105, 122,
        101, 32, 105, 110, 32, 75, 98, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__39_value:
    crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 115, 101, 114, 118, 101, 114, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 115, 116, 97, 114, 116, 32, 108, 101, 97, 110, 32, 105, 110, 32, 115, 101,
        114, 118, 101, 114, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_displayHelp___closed__40_value:
    crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        32, 32, 32, 32, 32, 32, 45, 45, 119, 111, 114, 107, 101, 114, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 115, 116, 97, 114, 116, 32, 108, 101, 97, 110, 32, 105, 110, 32, 115, 101,
        114, 118, 101, 114, 45, 119, 111, 114, 107, 101, 114, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_displayHelp___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_displayHelp___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 120, 95, 109, 101, 109, 111, 114, 121, 0]};
static mut l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7605406294670725603 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 104, 101, 108, 108, 0]};
static mut l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1219109238155592992 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10047197766011208281 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6431493749361951292 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 120, 77, 101, 109, 111, 114, 121, 0]};
static mut l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6364542185428301596 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Shell_0__Lean_maxMemory: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 105, 109, 101, 111, 117, 116, 0]};
static mut l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5864015424025905516 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13124628564013689175 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Shell_0__Lean_timeout: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [118, 101, 114, 98, 111, 115, 101, 0]};
static mut l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1069270177362153835 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_: u8 = 0;
static mut l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14501997214782607320 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Shell_0__Lean_verbose: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0: u32 = 0;
static mut l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1: u32 = 0;
pub static mut l___private_Lean_Shell_0__Lean_defaultTrustLevel: u32 = 0;
static mut l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0: u32 = 0;
pub static mut l___private_Lean_Shell_0__Lean_defaultNumThreads: u32 = 0;
static mut l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_value:
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
static mut l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_checkOptArg___closed__0_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        97, 114, 103, 117, 109, 101, 110, 116, 32, 109, 105, 115, 115, 105, 110, 103, 32, 102, 111,
        114, 32, 111, 112, 116, 105, 111, 110, 32, 39, 45, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_checkOptArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_checkOptArg___closed__1_value:
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
    m_data: [39, 0],
};
static mut l___private_Lean_Shell_0__Lean_checkOptArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 45, 68, 32, 112, 97, 114, 97, 109, 101, 116, 101,
        114, 44, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 109, 117, 115, 116, 32, 99, 111,
        110, 116, 97, 105, 110, 32, 39, 61, 39, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_setConfigOption___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_setConfigOption___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Shell_0__Lean_setConfigOption___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringString___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0_value:
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
    m_data: [10, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 114, 114, 111, 114, 58, 32, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0_value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [101, 114, 114, 111, 114, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 101, 114, 105, 99, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 111, 112, 116, 105, 111, 110, 32, 39, 45, 0]};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [39, 10, 0]};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 118, 97, 108,
        117, 101, 32, 102, 111, 114, 32, 39, 45, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1_value:
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
        39, 32, 105, 115, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 109, 109, 97, 110, 100, 32, 108, 105, 110,
        101, 32, 111, 112, 116, 105, 111, 110, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1_value:
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
    m_data: [69, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2_value:
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
    m_data: [117, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3_value:
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
    m_data: [108, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4_value:
    crate::leanh::LeanStringObject<57> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        45, 45, 108, 111, 97, 100, 45, 100, 121, 110, 108, 105, 98, 32, 105, 115, 32, 110, 111,
        116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32,
        82, 117, 115, 116, 47, 67, 97, 114, 103, 111, 32, 98, 97, 99, 107, 101, 110, 100, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5_value:
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
    m_data: [112, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6_value:
    crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        45, 45, 112, 108, 117, 103, 105, 110, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112,
        112, 111, 114, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 82, 117, 115, 116, 47,
        67, 97, 114, 103, 111, 32, 98, 97, 99, 107, 101, 110, 100, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7_value:
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
    m_data: [66, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8_value:
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
    m_data: [68, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9_value:
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
    m_data: [45, 68, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10_value:
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
    m_data: [116, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 118, 97, 108,
        117, 101, 32, 102, 111, 114, 32, 39, 45, 116, 39, 32, 105, 115, 32, 116, 111, 111, 32, 108,
        97, 114, 103, 101, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12_value:
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
    m_data: [45, 116, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109,
        101, 114, 105, 99, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 111,
        112, 116, 105, 111, 110, 32, 39, 45, 116, 39, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14_value:
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
    m_data: [84, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15_value:
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
    m_data: [45, 84, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109,
        101, 114, 105, 99, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 111,
        112, 116, 105, 111, 110, 32, 39, 45, 84, 39, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17_value:
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
    m_data: [77, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18_value:
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
    m_data: [45, 77, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109,
        101, 114, 105, 99, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 111,
        112, 116, 105, 111, 110, 32, 39, 45, 77, 39, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20_value:
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
    m_data: [82, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21_value:
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
    m_data: [45, 82, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22_value:
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
    m_data: [105, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23_value:
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
    m_data: [111, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24_value:
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
    m_data: [115, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 118, 97, 108,
        117, 101, 32, 102, 111, 114, 32, 39, 45, 115, 39, 32, 105, 115, 32, 116, 111, 111, 32, 108,
        97, 114, 103, 101, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27_value:
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
    m_data: [45, 115, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109,
        101, 114, 105, 99, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 111,
        112, 116, 105, 111, 110, 32, 39, 45, 115, 39, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29_value:
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
    m_data: [98, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30_value:
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
    m_data: [99, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31_value:
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
    m_data: [106, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 118, 97, 108,
        117, 101, 32, 102, 111, 114, 32, 39, 45, 106, 39, 32, 105, 115, 32, 116, 111, 111, 32, 108,
        97, 114, 103, 101, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33_value:
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
    m_data: [45, 106, 0],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        101, 114, 114, 111, 114, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109,
        101, 114, 105, 99, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 111,
        112, 116, 105, 111, 110, 32, 39, 45, 106, 39, 10, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [35, 108, 97, 110, 103, 0]};
static mut l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
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
        105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32,
        35, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__0: u8 = 0;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__1_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
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
        76, 76, 86, 77, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110,
        0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__2_value:
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
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__3_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
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
        82, 117, 115, 116, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111,
        110, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__6_value:
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
    m_data: [95, 117, 110, 105, 113, 0],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__7_value:
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
        core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__6_value)
            as *mut crate::leanh::LeanObject,
        3978731030111751661 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__8_value:
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
        core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__7_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__18_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 39, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__19_value:
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
    m_data: [95, 115, 116, 100, 105, 110, 0],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__20_value:
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
        core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__19_value)
            as *mut crate::leanh::LeanObject,
        5699004241150905893 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__21_value:
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
    m_data: [108, 101, 97, 110, 52, 0],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__24_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 108, 97, 110, 103, 117, 97, 103, 101, 32, 39, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__25_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 101, 120, 97, 99, 116, 108, 121, 32, 111, 110,
        101, 32, 102, 105, 108, 101, 32, 110, 97, 109, 101, 0,
    ],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Shell_0__Lean_shellMain___closed__26_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [60, 115, 116, 100, 105, 110, 62, 0],
};
static mut l___private_Lean_Shell_0__Lean_shellMain___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Shell_0__Lean_shellMain___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(
    mut v_a_3191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3192_ = lean_decode_lossy_utf8(v_a_3191_);
    crate::leanh::lean_dec_ref(v_a_3191_);
    return v_res_3192_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_runMain___boxed(
    mut v_env_3197_: *mut crate::leanh::LeanObject,
    mut v_opts_3198_: *mut crate::leanh::LeanObject,
    mut v_args_3199_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3201_: u32 = 0;
    let mut v_r_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3201_ = lean_eval_main(v_env_3197_, v_opts_3198_, v_args_3199_);
    crate::leanh::lean_dec(v_args_3199_);
    crate::leanh::lean_dec_ref(v_opts_3198_);
    crate::leanh::lean_dec_ref(v_env_3197_);
    v_r_3202_ = crate::leanh::lean_box_uint32(v_res_3201_);
    return v_r_3202_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_initLLVM___boxed(
    mut v_a_00___x40___internal___hyg_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3205_ = lean_init_llvm();
    return v_res_3205_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_emitLLVM___boxed(
    mut v_env_3210_: *mut crate::leanh::LeanObject,
    mut v_modName_3211_: *mut crate::leanh::LeanObject,
    mut v_filepath_3212_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3214_ = lean_emit_llvm(v_env_3210_, v_modName_3211_, v_filepath_3212_);
    return v_res_3214_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(
    mut v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3217_: u8 = 0;
    let mut v_r_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ = lean_internal_has_address_sanitizer(
        v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_3216_,
    );
    v_r_3218_ = crate::leanh::lean_box((v_res_3217_) as usize);
    return v_r_3218_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(
    mut v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_3220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3221_: u8 = 0;
    let mut v_r_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3221_ =
        lean_internal_is_multi_thread(v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_3220_);
    v_r_3222_ = crate::leanh::lean_box((v_res_3221_) as usize);
    return v_r_3222_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(
    mut v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_3224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3225_: u8 = 0;
    let mut v_r_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3225_ = lean_internal_is_debug(v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_3224_);
    v_r_3226_ = crate::leanh::lean_box((v_res_3225_) as usize);
    return v_r_3226_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(
    mut v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_3228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3229_ =
        lean_internal_get_build_type(v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_3228_);
    return v_res_3229_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(
    mut v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_3231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3232_ = lean_internal_get_default_max_memory(
        v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_3231_,
    );
    return v_res_3232_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(
    mut v_max_3235_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_max_boxed_3237_: usize = 0;
    let mut v_res_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_max_boxed_3237_ = crate::leanh::lean_unbox_usize(v_max_3235_);
    crate::leanh::lean_dec(v_max_3235_);
    v_res_3238_ = lean_internal_set_max_memory(v_max_boxed_3237_);
    return v_res_3238_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(
    mut v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ = lean_internal_get_default_max_heartbeat(
        v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_3240_,
    );
    return v_res_3241_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(
    mut v_max_3244_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_max_boxed_3246_: usize = 0;
    let mut v_res_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_max_boxed_3246_ = crate::leanh::lean_unbox_usize(v_max_3244_);
    crate::leanh::lean_dec(v_max_3244_);
    v_res_3247_ = lean_internal_set_max_heartbeat(v_max_boxed_3246_);
    return v_res_3247_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose___boxed(
    mut v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3250_: u8 = 0;
    let mut v_r_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3250_ =
        lean_internal_get_default_verbose(v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_3249_);
    v_r_3251_ = crate::leanh::lean_box((v_res_3250_) as usize);
    return v_r_3251_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_setExitOnPanic___boxed(
    mut v_exit_3254_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exit_boxed_3256_: u8 = 0;
    let mut v_res_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_exit_boxed_3256_ = (crate::leanh::lean_unbox(v_exit_3254_) as u8);
    v_res_3257_ = lean_internal_set_exit_on_panic(v_exit_boxed_3256_);
    return v_res_3257_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize___boxed(
    mut v_sz_3260_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3262_: usize = 0;
    let mut v_res_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3262_ = crate::leanh::lean_unbox_usize(v_sz_3260_);
    crate::leanh::lean_dec(v_sz_3260_);
    v_res_3263_ = lean_internal_set_thread_stack_size(v_sz_boxed_3262_);
    return v_res_3263_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_enableDebug___boxed(
    mut v_tag_3266_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3268_ = lean_internal_enable_debug(v_tag_3266_);
    crate::leanh::lean_dec_ref(v_tag_3266_);
    return v_res_3268_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1() -> u8 {
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    v___x_3270_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
    v___x_3271_ = l_Lean_version_specialDesc;
    v___x_3272_ = lean_string_dec_eq(v___x_3271_, v___x_3270_);
    return v___x_3272_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__2;
    v___x_3275_ = l_Lean_versionStringCore;
    v___x_3276_ = lean_string_append(v___x_3275_, v___x_3274_);
    return v___x_3276_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3277_ = l_Lean_version_specialDesc;
    v___x_3278_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__3),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once),
        _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3,
    );
    v___x_3279_ = lean_string_append(v___x_3278_, v___x_3277_);
    return v___x_3279_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3281_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
    v___x_3282_ = l_Lean_versionStringCore;
    v___x_3283_ = lean_string_append(v___x_3282_, v___x_3281_);
    return v___x_3283_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shortVersionString()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3284_: u8 = 0;
    v___x_3284_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__1),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once),
        _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1,
    );
    if v___x_3284_ == 0 {
        let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3285_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shortVersionString___closed__4),
            core::ptr::addr_of_mut!(
                l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once
            ),
            _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4,
        );
        return v___x_3285_;
    } else {
        let mut v___x_3286_: u8 = 0;
        v___x_3286_ = l_Lean_version_isRelease;
        if v___x_3286_ == 0 {
            let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3287_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_Shell_0__Lean_shortVersionString___closed__6
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once
                ),
                _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6,
            );
            return v___x_3287_;
        } else {
            let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3288_ = l_Lean_versionStringCore;
            return v___x_3288_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3291_ = crate::leanh::lean_box(0);
    v___x_3292_ = lean_internal_get_build_type(v___x_3291_);
    return v___x_3292_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4() -> u8 {
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: u8 = 0;
    v___x_3294_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
    v___x_3295_ = l_Lean_githash;
    v___x_3296_ = lean_string_dec_eq(v___x_3295_, v___x_3294_);
    return v___x_3296_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6() -> u8 {
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: u8 = 0;
    v___x_3298_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
    v___x_3299_ = l_System_Platform_target;
    v___x_3300_ = lean_string_dec_eq(v___x_3299_, v___x_3298_);
    return v___x_3300_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
    v_ver_3302_ = l___private_Lean_Shell_0__Lean_shortVersionString;
    v___x_3303_ = lean_string_append(v_ver_3302_, v___x_3301_);
    return v___x_3303_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3304_ = l_System_Platform_target;
    v___x_3305_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_versionHeader___closed__7),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once),
        _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7,
    );
    v_ver_3306_ = lean_string_append(v___x_3305_, v___x_3304_);
    return v_ver_3306_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_versionHeader() -> *mut crate::leanh::LeanObject
{
    let mut v_ver_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u8 = 0;
    let mut v_ver_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ver_3324_ = l___private_Lean_Shell_0__Lean_shortVersionString;
                v___x_3325_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_versionHeader___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once
                    ),
                    _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6,
                );
                if v___x_3325_ == 0 {
                    v_ver_3326_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Shell_0__Lean_versionHeader___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once
                        ),
                        _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8,
                    );
                    v_ver_3318_ = v_ver_3326_;
                    state = 2;
                    continue;
                } else {
                    v_ver_3318_ = v_ver_3324_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3309_ = l___private_Lean_Shell_0__Lean_versionHeader___closed__0;
                v___x_3310_ = lean_string_append(v___x_3309_, v_ver_3308_);
                crate::leanh::lean_dec_ref(v_ver_3308_);
                v___x_3311_ = l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
                v___x_3312_ = lean_string_append(v___x_3310_, v___x_3311_);
                v___x_3313_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_versionHeader___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once
                    ),
                    _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2,
                );
                v___x_3314_ = lean_string_append(v___x_3312_, v___x_3313_);
                v___x_3315_ = l___private_Lean_Shell_0__Lean_versionHeader___closed__3;
                v___x_3316_ = lean_string_append(v___x_3314_, v___x_3315_);
                return v___x_3316_;
            }
            2 => {
                v___x_3319_ = l_Lean_githash;
                v___x_3320_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_versionHeader___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once
                    ),
                    _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4,
                );
                if v___x_3320_ == 0 {
                    v___x_3321_ = l___private_Lean_Shell_0__Lean_versionHeader___closed__5;
                    crate::leanh::lean_inc_ref(v_ver_3318_);
                    v___x_3322_ = lean_string_append(v_ver_3318_, v___x_3321_);
                    v_ver_3323_ = lean_string_append(v___x_3322_, v___x_3319_);
                    v_ver_3308_ = v_ver_3323_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_ver_3318_);
                    v_ver_3308_ = v_ver_3318_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0() -> u8 {
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    v___x_3327_ = crate::leanh::lean_box(0);
    v___x_3328_ = lean_internal_has_llvm_backend(v___x_3327_);
    return v___x_3328_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_featuresString() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3331_: u8 = 0;
    v___x_3331_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_featuresString___closed__0),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_featuresString___closed__0_once),
        _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0,
    );
    if v___x_3331_ == 0 {
        let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3332_ = l___private_Lean_Shell_0__Lean_featuresString___closed__1;
        return v___x_3332_;
    } else {
        let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3333_ = l___private_Lean_Shell_0__Lean_featuresString___closed__2;
        return v___x_3333_;
    }
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12() -> u8 {
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    v___x_3346_ = crate::leanh::lean_box(0);
    v___x_3347_ = lean_internal_is_debug(v___x_3346_);
    return v___x_3347_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36() -> u8 {
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    v___x_3371_ = crate::leanh::lean_box(0);
    v___x_3372_ = lean_internal_is_multi_thread(v___x_3371_);
    return v___x_3372_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_displayHelp(
    mut v_useStderr_3377_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useStderr_3377_ == 0 {
                    v___x_3467_ = lean_get_stdout();
                    v_out_3411_ = v___x_3467_;
                    state = 3;
                    continue;
                } else {
                    v___x_3468_ = lean_get_stderr();
                    v_out_3411_ = v___x_3468_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3381_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__0;
                v___x_3382_ = l_IO_FS_Stream_putStrLn(v___y_3380_, v___x_3381_);
                return v___x_3382_;
            }
            2 => {
                v___x_3385_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__1;
                crate::leanh::lean_inc_ref(v___y_3384_);
                v___x_3386_ = l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3385_);
                if crate::leanh::lean_obj_tag(v___x_3386_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3386_, 1);
                    v___x_3387_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__2;
                    crate::leanh::lean_inc_ref(v___y_3384_);
                    v___x_3388_ = l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3387_);
                    if crate::leanh::lean_obj_tag(v___x_3388_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3388_, 1);
                        v___x_3389_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__3;
                        crate::leanh::lean_inc_ref(v___y_3384_);
                        v___x_3390_ = l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3389_);
                        if crate::leanh::lean_obj_tag(v___x_3390_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3390_, 1);
                            v___x_3391_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__4;
                            crate::leanh::lean_inc_ref(v___y_3384_);
                            v___x_3392_ = l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3391_);
                            if crate::leanh::lean_obj_tag(v___x_3392_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3392_, 1);
                                v___x_3393_ =
                                    l___private_Lean_Shell_0__Lean_displayHelp___closed__5;
                                crate::leanh::lean_inc_ref(v___y_3384_);
                                v___x_3394_ = l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3393_);
                                if crate::leanh::lean_obj_tag(v___x_3394_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3394_, 1);
                                    v___x_3395_ =
                                        l___private_Lean_Shell_0__Lean_displayHelp___closed__6;
                                    crate::leanh::lean_inc_ref(v___y_3384_);
                                    v___x_3396_ = l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3395_);
                                    if crate::leanh::lean_obj_tag(v___x_3396_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3396_, 1);
                                        v___x_3397_ =
                                            l___private_Lean_Shell_0__Lean_displayHelp___closed__7;
                                        crate::leanh::lean_inc_ref(v___y_3384_);
                                        v___x_3398_ =
                                            l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3397_);
                                        if crate::leanh::lean_obj_tag(v___x_3398_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3398_, 1);
                                            v___x_3399_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__8;
                                            crate::leanh::lean_inc_ref(v___y_3384_);
                                            v___x_3400_ =
                                                l_IO_FS_Stream_putStrLn(v___y_3384_, v___x_3399_);
                                            if crate::leanh::lean_obj_tag(v___x_3400_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3400_, 1);
                                                v___x_3401_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__9;
                                                crate::leanh::lean_inc_ref(v___y_3384_);
                                                v___x_3402_ = l_IO_FS_Stream_putStrLn(
                                                    v___y_3384_,
                                                    v___x_3401_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_3402_) == 0 {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3402_,
                                                        1,
                                                    );
                                                    v___x_3403_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__10;
                                                    crate::leanh::lean_inc_ref(v___y_3384_);
                                                    v___x_3404_ = l_IO_FS_Stream_putStrLn(
                                                        v___y_3384_,
                                                        v___x_3403_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_3404_) == 0
                                                    {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3404_,
                                                            1,
                                                        );
                                                        v___x_3405_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__11;
                                                        crate::leanh::lean_inc_ref(v___y_3384_);
                                                        v___x_3406_ = l_IO_FS_Stream_putStrLn(
                                                            v___y_3384_,
                                                            v___x_3405_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_3406_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_3406_,
                                                                1,
                                                            );
                                                            v___x_3407_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once), _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
                                                            if v___x_3407_ == 0 {
                                                                v___y_3380_ = v___y_3384_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_3408_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__13;
                                                                crate::leanh::lean_inc_ref(
                                                                    v___y_3384_,
                                                                );
                                                                v___x_3409_ =
                                                                    l_IO_FS_Stream_putStrLn(
                                                                        v___y_3384_,
                                                                        v___x_3408_,
                                                                    );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_3409_,
                                                                ) == 0
                                                                {
                                                                    crate::leanh::lean_dec_ref_known(v___x_3409_, 1);
                                                                    v___y_3380_ = v___y_3384_;
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_3384_,
                                                                    );
                                                                    return v___x_3409_;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___y_3384_);
                                                            return v___x_3406_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___y_3384_);
                                                        return v___x_3404_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___y_3384_);
                                                    return v___x_3402_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___y_3384_);
                                                return v___x_3400_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___y_3384_);
                                            return v___x_3398_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___y_3384_);
                                        return v___x_3396_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___y_3384_);
                                    return v___x_3394_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___y_3384_);
                                return v___x_3392_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_3384_);
                            return v___x_3390_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3384_);
                        return v___x_3388_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3384_);
                    return v___x_3386_;
                }
            }
            3 => {
                v___x_3412_ = l___private_Lean_Shell_0__Lean_versionHeader;
                crate::leanh::lean_inc_ref(v_out_3411_);
                v___x_3413_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3412_);
                if crate::leanh::lean_obj_tag(v___x_3413_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3413_, 1);
                    v___x_3414_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__14;
                    crate::leanh::lean_inc_ref(v_out_3411_);
                    v___x_3415_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3414_);
                    if crate::leanh::lean_obj_tag(v___x_3415_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3415_, 1);
                        v___x_3416_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__15;
                        crate::leanh::lean_inc_ref(v_out_3411_);
                        v___x_3417_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3416_);
                        if crate::leanh::lean_obj_tag(v___x_3417_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3417_, 1);
                            v___x_3418_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
                            crate::leanh::lean_inc_ref(v_out_3411_);
                            v___x_3419_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3418_);
                            if crate::leanh::lean_obj_tag(v___x_3419_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3419_, 1);
                                v___x_3420_ =
                                    l___private_Lean_Shell_0__Lean_displayHelp___closed__17;
                                crate::leanh::lean_inc_ref(v_out_3411_);
                                v___x_3421_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3420_);
                                if crate::leanh::lean_obj_tag(v___x_3421_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3421_, 1);
                                    v___x_3422_ =
                                        l___private_Lean_Shell_0__Lean_displayHelp___closed__18;
                                    crate::leanh::lean_inc_ref(v_out_3411_);
                                    v___x_3423_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3422_);
                                    if crate::leanh::lean_obj_tag(v___x_3423_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3423_, 1);
                                        v___x_3424_ =
                                            l___private_Lean_Shell_0__Lean_displayHelp___closed__19;
                                        crate::leanh::lean_inc_ref(v_out_3411_);
                                        v___x_3425_ =
                                            l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3424_);
                                        if crate::leanh::lean_obj_tag(v___x_3425_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3425_, 1);
                                            v___x_3426_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__20;
                                            crate::leanh::lean_inc_ref(v_out_3411_);
                                            v___x_3427_ =
                                                l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3426_);
                                            if crate::leanh::lean_obj_tag(v___x_3427_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3427_, 1);
                                                v___x_3428_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__21;
                                                crate::leanh::lean_inc_ref(v_out_3411_);
                                                v___x_3429_ = l_IO_FS_Stream_putStrLn(
                                                    v_out_3411_,
                                                    v___x_3428_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_3429_) == 0 {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3429_,
                                                        1,
                                                    );
                                                    v___x_3430_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__22;
                                                    crate::leanh::lean_inc_ref(v_out_3411_);
                                                    v___x_3431_ = l_IO_FS_Stream_putStrLn(
                                                        v_out_3411_,
                                                        v___x_3430_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_3431_) == 0
                                                    {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3431_,
                                                            1,
                                                        );
                                                        v___x_3432_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__23;
                                                        crate::leanh::lean_inc_ref(v_out_3411_);
                                                        v___x_3433_ = l_IO_FS_Stream_putStrLn(
                                                            v_out_3411_,
                                                            v___x_3432_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_3433_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_3433_,
                                                                1,
                                                            );
                                                            v___x_3434_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__24;
                                                            crate::leanh::lean_inc_ref(v_out_3411_);
                                                            v___x_3435_ = l_IO_FS_Stream_putStrLn(
                                                                v_out_3411_,
                                                                v___x_3434_,
                                                            );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3435_,
                                                            ) == 0
                                                            {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_3435_,
                                                                    1,
                                                                );
                                                                v___x_3436_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__25;
                                                                crate::leanh::lean_inc_ref(
                                                                    v_out_3411_,
                                                                );
                                                                v___x_3437_ =
                                                                    l_IO_FS_Stream_putStrLn(
                                                                        v_out_3411_,
                                                                        v___x_3436_,
                                                                    );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_3437_,
                                                                ) == 0
                                                                {
                                                                    crate::leanh::lean_dec_ref_known(v___x_3437_, 1);
                                                                    v___x_3438_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__26;
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_out_3411_,
                                                                    );
                                                                    v___x_3439_ =
                                                                        l_IO_FS_Stream_putStrLn(
                                                                            v_out_3411_,
                                                                            v___x_3438_,
                                                                        );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_3439_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec_ref_known(v___x_3439_, 1);
                                                                        v___x_3440_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__27;
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_out_3411_,
                                                                        );
                                                                        v___x_3441_ =
                                                                            l_IO_FS_Stream_putStrLn(
                                                                                v_out_3411_,
                                                                                v___x_3440_,
                                                                            );
                                                                        if crate::leanh::lean_obj_tag(v___x_3441_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3441_, 1);
v___x_3442_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__28;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3443_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3442_);
if crate::leanh::lean_obj_tag(v___x_3443_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3443_, 1);
v___x_3444_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__29;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3445_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3444_);
if crate::leanh::lean_obj_tag(v___x_3445_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3445_, 1);
v___x_3446_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__30;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3447_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3446_);
if crate::leanh::lean_obj_tag(v___x_3447_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3447_, 1);
v___x_3448_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__31;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3449_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3448_);
if crate::leanh::lean_obj_tag(v___x_3449_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3449_, 1);
v___x_3450_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__32;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3451_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3450_);
if crate::leanh::lean_obj_tag(v___x_3451_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3451_, 1);
v___x_3452_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__33;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3453_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3452_);
if crate::leanh::lean_obj_tag(v___x_3453_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3453_, 1);
v___x_3454_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__34;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3455_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3454_);
if crate::leanh::lean_obj_tag(v___x_3455_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3455_, 1);
v___x_3456_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__35;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3457_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3456_);
if crate::leanh::lean_obj_tag(v___x_3457_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3457_, 1);
v___x_3458_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once), _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if v___x_3458_ == 0 {
v___y_3384_ = v_out_3411_;
state = 2; continue;
} else {
v___x_3459_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__37;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3460_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3459_);
if crate::leanh::lean_obj_tag(v___x_3460_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3460_, 1);
v___x_3461_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__38;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3462_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3461_);
if crate::leanh::lean_obj_tag(v___x_3462_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3462_, 1);
v___x_3463_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__39;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3464_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3463_);
if crate::leanh::lean_obj_tag(v___x_3464_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3464_, 1);
v___x_3465_ = l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
crate::leanh::lean_inc_ref(v_out_3411_);
v___x_3466_ = l_IO_FS_Stream_putStrLn(v_out_3411_, v___x_3465_);
if crate::leanh::lean_obj_tag(v___x_3466_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_3466_, 1);
v___y_3384_ = v_out_3411_;
state = 2; continue;
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3466_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3464_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3462_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3460_;
}
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3457_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3455_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3453_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3451_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3449_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3447_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3445_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3443_;
}
} else {
crate::leanh::lean_dec_ref(v_out_3411_);
return v___x_3441_;
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_out_3411_,
                                                                        );
                                                                        return v___x_3439_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_out_3411_,
                                                                    );
                                                                    return v___x_3437_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_out_3411_,
                                                                );
                                                                return v___x_3435_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_out_3411_);
                                                            return v___x_3433_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_out_3411_);
                                                        return v___x_3431_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_out_3411_);
                                                    return v___x_3429_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_out_3411_);
                                                return v___x_3427_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_out_3411_);
                                            return v___x_3425_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_out_3411_);
                                        return v___x_3423_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_out_3411_);
                                    return v___x_3421_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_out_3411_);
                                return v___x_3419_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_out_3411_);
                            return v___x_3417_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_out_3411_);
                        return v___x_3415_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_out_3411_);
                    return v___x_3413_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_displayHelp___boxed(
    mut v_useStderr_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useStderr_boxed_3471_: u8 = 0;
    let mut v_res_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useStderr_boxed_3471_ = (crate::leanh::lean_unbox(v_useStderr_3469_) as u8);
    v_res_3472_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_boxed_3471_);
    return v_res_3472_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(
    mut v_x_3473_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3473_ {
        0 => {
            let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3474_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3474_;
        }
        1 => {
            let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3475_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3475_;
        }
        _ => {
            let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3476_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3476_;
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(
    mut v_x_3477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3478_: u8 = 0;
    let mut v_res_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3478_ = (crate::leanh::lean_unbox(v_x_3477_) as u8);
    v_res_3479_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_boxed_3478_);
    return v_res_3479_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(
    mut v_x_3480_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3481_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_3480_);
    return v___x_3481_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(
    mut v_x_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3483_: u8 = 0;
    let mut v_res_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3483_ = (crate::leanh::lean_unbox(v_x_3482_) as u8);
    v_res_3484_ = l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(v_x_4__boxed_3483_);
    return v_res_3484_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(
    mut v_k_3485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3485_);
    return v_k_3485_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(
    mut v_k_3486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3487_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_3486_);
    crate::leanh::lean_dec(v_k_3486_);
    return v_res_3487_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(
    mut v_motive_3488_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3489_: *mut crate::leanh::LeanObject,
    mut v_t_3490_: u8,
    mut v_h_3491_: *mut crate::leanh::LeanObject,
    mut v_k_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3492_);
    return v_k_3492_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(
    mut v_motive_3493_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3494_: *mut crate::leanh::LeanObject,
    mut v_t_3495_: *mut crate::leanh::LeanObject,
    mut v_h_3496_: *mut crate::leanh::LeanObject,
    mut v_k_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3498_: u8 = 0;
    let mut v_res_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3498_ = (crate::leanh::lean_unbox(v_t_3495_) as u8);
    v_res_3499_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(
        v_motive_3493_,
        v_ctorIdx_3494_,
        v_t_boxed_3498_,
        v_h_3496_,
        v_k_3497_,
    );
    crate::leanh::lean_dec(v_k_3497_);
    crate::leanh::lean_dec(v_ctorIdx_3494_);
    return v_res_3499_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(
    mut v_frontend_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_frontend_3500_);
    return v_frontend_3500_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(
    mut v_frontend_3501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3502_ =
        l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_3501_);
    crate::leanh::lean_dec(v_frontend_3501_);
    return v_res_3502_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(
    mut v_motive_3503_: *mut crate::leanh::LeanObject,
    mut v_t_3504_: u8,
    mut v_h_3505_: *mut crate::leanh::LeanObject,
    mut v_frontend_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_frontend_3506_);
    return v_frontend_3506_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(
    mut v_motive_3507_: *mut crate::leanh::LeanObject,
    mut v_t_3508_: *mut crate::leanh::LeanObject,
    mut v_h_3509_: *mut crate::leanh::LeanObject,
    mut v_frontend_3510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3511_: u8 = 0;
    let mut v_res_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3511_ = (crate::leanh::lean_unbox(v_t_3508_) as u8);
    v_res_3512_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(
        v_motive_3507_,
        v_t_boxed_3511_,
        v_h_3509_,
        v_frontend_3510_,
    );
    crate::leanh::lean_dec(v_frontend_3510_);
    return v_res_3512_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(
    mut v_watchdog_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_watchdog_3513_);
    return v_watchdog_3513_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(
    mut v_watchdog_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3515_ =
        l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(v_watchdog_3514_);
    crate::leanh::lean_dec(v_watchdog_3514_);
    return v_res_3515_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(
    mut v_motive_3516_: *mut crate::leanh::LeanObject,
    mut v_t_3517_: u8,
    mut v_h_3518_: *mut crate::leanh::LeanObject,
    mut v_watchdog_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_watchdog_3519_);
    return v_watchdog_3519_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(
    mut v_motive_3520_: *mut crate::leanh::LeanObject,
    mut v_t_3521_: *mut crate::leanh::LeanObject,
    mut v_h_3522_: *mut crate::leanh::LeanObject,
    mut v_watchdog_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3524_: u8 = 0;
    let mut v_res_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3524_ = (crate::leanh::lean_unbox(v_t_3521_) as u8);
    v_res_3525_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(
        v_motive_3520_,
        v_t_boxed_3524_,
        v_h_3522_,
        v_watchdog_3523_,
    );
    crate::leanh::lean_dec(v_watchdog_3523_);
    return v_res_3525_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(
    mut v_worker_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_worker_3526_);
    return v_worker_3526_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(
    mut v_worker_3527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3528_ =
        l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_3527_);
    crate::leanh::lean_dec(v_worker_3527_);
    return v_res_3528_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(
    mut v_motive_3529_: *mut crate::leanh::LeanObject,
    mut v_t_3530_: u8,
    mut v_h_3531_: *mut crate::leanh::LeanObject,
    mut v_worker_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_worker_3532_);
    return v_worker_3532_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(
    mut v_motive_3533_: *mut crate::leanh::LeanObject,
    mut v_t_3534_: *mut crate::leanh::LeanObject,
    mut v_h_3535_: *mut crate::leanh::LeanObject,
    mut v_worker_3536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3537_: u8 = 0;
    let mut v_res_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3537_ = (crate::leanh::lean_unbox(v_t_3534_) as u8);
    v_res_3538_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(
        v_motive_3533_,
        v_t_boxed_3537_,
        v_h_3535_,
        v_worker_3536_,
    );
    crate::leanh::lean_dec(v_worker_3536_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(
    mut v_name_3539_: *mut crate::leanh::LeanObject,
    mut v_decl_3540_: *mut crate::leanh::LeanObject,
    mut v_ref_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3551_: u8 = 0;
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3556_: u8 = 0;
    let mut v_unused_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3561_: u8 = 0;
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3543_ = crate::leanh::lean_ctor_get(v_decl_3540_, 0);
                v_descr_3544_ = crate::leanh::lean_ctor_get(v_decl_3540_, 1);
                v_deprecation_x3f_3545_ = crate::leanh::lean_ctor_get(v_decl_3540_, 2);
                crate::leanh::lean_inc(v_defValue_3543_);
                v___x_3546_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3546_, 0, v_defValue_3543_);
                crate::leanh::lean_inc(v_deprecation_x3f_3545_);
                crate::leanh::lean_inc_ref(v_descr_3544_);
                crate::leanh::lean_inc_n(v_name_3539_, 2);
                v___x_3547_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3547_, 0, v_name_3539_);
                crate::leanh::lean_ctor_set(v___x_3547_, 1, v_ref_3541_);
                crate::leanh::lean_ctor_set(v___x_3547_, 2, v___x_3546_);
                crate::leanh::lean_ctor_set(v___x_3547_, 3, v_descr_3544_);
                crate::leanh::lean_ctor_set(v___x_3547_, 4, v_deprecation_x3f_3545_);
                v___x_3548_ = lean_register_option(v_name_3539_, v___x_3547_);
                if crate::leanh::lean_obj_tag(v___x_3548_) == 0 {
                    v_isSharedCheck_3556_ = (!crate::leanh::lean_is_exclusive(v___x_3548_)) as u8;
                    if v_isSharedCheck_3556_ == 0 {
                        v_unused_3557_ = crate::leanh::lean_ctor_get(v___x_3548_, 0);
                        crate::leanh::lean_dec(v_unused_3557_);
                        v___x_3550_ = v___x_3548_;
                        v_isShared_3551_ = v_isSharedCheck_3556_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3548_);
                        v___x_3550_ = crate::leanh::lean_box(0);
                        v_isShared_3551_ = v_isSharedCheck_3556_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3539_);
                    v_a_3558_ = crate::leanh::lean_ctor_get(v___x_3548_, 0);
                    v_isSharedCheck_3565_ = (!crate::leanh::lean_is_exclusive(v___x_3548_)) as u8;
                    if v_isSharedCheck_3565_ == 0 {
                        v___x_3560_ = v___x_3548_;
                        v_isShared_3561_ = v_isSharedCheck_3565_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3558_);
                        crate::leanh::lean_dec(v___x_3548_);
                        v___x_3560_ = crate::leanh::lean_box(0);
                        v_isShared_3561_ = v_isSharedCheck_3565_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3543_);
                v___x_3552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3552_, 0, v_name_3539_);
                crate::leanh::lean_ctor_set(v___x_3552_, 1, v_defValue_3543_);
                if v_isShared_3551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3552_);
                    v___x_3554_ = v___x_3550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
                    v___x_3554_ = v_reuseFailAlloc_3555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3554_;
            }
            3 => {
                if v_isShared_3561_ == 0 {
                    v___x_3563_ = v___x_3560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
                    v___x_3563_ = v_reuseFailAlloc_3564_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(
    mut v_name_3566_: *mut crate::leanh::LeanObject,
    mut v_decl_3567_: *mut crate::leanh::LeanObject,
    mut v_ref_3568_: *mut crate::leanh::LeanObject,
    mut v_a_3569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3570_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_3566_, v_decl_3567_, v_ref_3568_);
    crate::leanh::lean_dec_ref(v_decl_3567_);
    return v_res_3570_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3574_ = crate::leanh::lean_box(0);
    v___x_3575_ = lean_internal_get_default_max_memory(v___x_3574_);
    return v___x_3575_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3576_ = crate::leanh::lean_box(0);
    v___x_3577_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
    v___x_3578_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once), _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
    v___x_3579_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
    crate::leanh::lean_ctor_set(v___x_3579_, 1, v___x_3577_);
    crate::leanh::lean_ctor_set(v___x_3579_, 2, v___x_3576_);
    return v___x_3579_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
    v___x_3604_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once), _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
    v___x_3605_ = l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
    v___x_3606_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_3603_, v___x_3604_, v___x_3605_);
    return v___x_3606_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(
    mut v_a_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ =
        l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
    return v_res_3608_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ = crate::leanh::lean_box(0);
    v___x_3613_ = lean_internal_get_default_max_heartbeat(v___x_3612_);
    return v___x_3613_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = crate::leanh::lean_box(0);
    v___x_3615_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
    v___x_3616_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once), _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
    v___x_3617_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3617_, 0, v___x_3616_);
    crate::leanh::lean_ctor_set(v___x_3617_, 1, v___x_3615_);
    crate::leanh::lean_ctor_set(v___x_3617_, 2, v___x_3614_);
    return v___x_3617_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3622_ = l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
    v___x_3623_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once), _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
    v___x_3624_ = l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
    v___x_3625_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_3622_, v___x_3623_, v___x_3624_);
    return v___x_3625_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(
    mut v_a_3626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3627_ =
        l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
    return v_res_3627_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(
    mut v_name_3628_: *mut crate::leanh::LeanObject,
    mut v_decl_3629_: *mut crate::leanh::LeanObject,
    mut v_ref_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_unused_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3632_ = crate::leanh::lean_ctor_get(v_decl_3629_, 0);
                v_descr_3633_ = crate::leanh::lean_ctor_get(v_decl_3629_, 1);
                v_deprecation_x3f_3634_ = crate::leanh::lean_ctor_get(v_decl_3629_, 2);
                v___x_3635_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3636_ = (crate::leanh::lean_unbox(v_defValue_3632_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_3635_, 0 as u32, v___x_3636_);
                crate::leanh::lean_inc(v_deprecation_x3f_3634_);
                crate::leanh::lean_inc_ref(v_descr_3633_);
                crate::leanh::lean_inc_n(v_name_3628_, 2);
                v___x_3637_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3637_, 0, v_name_3628_);
                crate::leanh::lean_ctor_set(v___x_3637_, 1, v_ref_3630_);
                crate::leanh::lean_ctor_set(v___x_3637_, 2, v___x_3635_);
                crate::leanh::lean_ctor_set(v___x_3637_, 3, v_descr_3633_);
                crate::leanh::lean_ctor_set(v___x_3637_, 4, v_deprecation_x3f_3634_);
                v___x_3638_ = lean_register_option(v_name_3628_, v___x_3637_);
                if crate::leanh::lean_obj_tag(v___x_3638_) == 0 {
                    v_isSharedCheck_3646_ = (!crate::leanh::lean_is_exclusive(v___x_3638_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v_unused_3647_ = crate::leanh::lean_ctor_get(v___x_3638_, 0);
                        crate::leanh::lean_dec(v_unused_3647_);
                        v___x_3640_ = v___x_3638_;
                        v_isShared_3641_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3638_);
                        v___x_3640_ = crate::leanh::lean_box(0);
                        v_isShared_3641_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3628_);
                    v_a_3648_ = crate::leanh::lean_ctor_get(v___x_3638_, 0);
                    v_isSharedCheck_3655_ = (!crate::leanh::lean_is_exclusive(v___x_3638_)) as u8;
                    if v_isSharedCheck_3655_ == 0 {
                        v___x_3650_ = v___x_3638_;
                        v_isShared_3651_ = v_isSharedCheck_3655_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3648_);
                        crate::leanh::lean_dec(v___x_3638_);
                        v___x_3650_ = crate::leanh::lean_box(0);
                        v_isShared_3651_ = v_isSharedCheck_3655_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3632_);
                v___x_3642_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3642_, 0, v_name_3628_);
                crate::leanh::lean_ctor_set(v___x_3642_, 1, v_defValue_3632_);
                if v_isShared_3641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3640_, 0, v___x_3642_);
                    v___x_3644_ = v___x_3640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3644_;
            }
            3 => {
                if v_isShared_3651_ == 0 {
                    v___x_3653_ = v___x_3650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
                    v___x_3653_ = v_reuseFailAlloc_3654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(
    mut v_name_3656_: *mut crate::leanh::LeanObject,
    mut v_decl_3657_: *mut crate::leanh::LeanObject,
    mut v_ref_3658_: *mut crate::leanh::LeanObject,
    mut v_a_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3660_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_3656_, v_decl_3657_, v_ref_3658_);
    crate::leanh::lean_dec_ref(v_decl_3657_);
    return v_res_3660_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_()
-> u8 {
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: u8 = 0;
    v___x_3664_ = crate::leanh::lean_box(0);
    v___x_3665_ = lean_internal_get_default_verbose(v___x_3664_);
    return v___x_3665_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3666_ = crate::leanh::lean_box(0);
    v___x_3667_ = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
    v___x_3668_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once), _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
    v___x_3669_ = crate::leanh::lean_box((v___x_3668_) as usize);
    v___x_3670_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3670_, 0, v___x_3669_);
    crate::leanh::lean_ctor_set(v___x_3670_, 1, v___x_3667_);
    crate::leanh::lean_ctor_set(v___x_3670_, 2, v___x_3666_);
    return v___x_3670_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3675_ = l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_;
    v___x_3676_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once), _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
    v___x_3677_ = l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_;
    v___x_3678_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_3675_, v___x_3676_, v___x_3677_);
    return v___x_3678_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(
    mut v_a_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3680_ =
        l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
    return v_res_3680_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_getDefaultOptions___boxed(
    mut v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3683_ =
        lean_internal_get_default_options(v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_3682_);
    return v_res_3683_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(
    mut v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3686_: u32 = 0;
    let mut v_r_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = lean_internal_get_believer_trust_level(
        v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_3685_,
    );
    v_r_3687_ = crate::leanh::lean_box_uint32(v_res_3686_);
    return v_r_3687_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0() -> u32 {
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: u32 = 0;
    v___x_3688_ = crate::leanh::lean_box(0);
    v___x_3689_ = lean_internal_get_believer_trust_level(v___x_3688_);
    return v___x_3689_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1() -> u32 {
    let mut v___x_3690_: u32 = 0;
    let mut v___x_3691_: u32 = 0;
    let mut v___x_3692_: u32 = 0;
    v___x_3690_ = 1;
    v___x_3691_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once),
        _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0,
    );
    v___x_3692_ = lean_uint32_add(v___x_3691_, v___x_3690_);
    return v___x_3692_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel() -> u32 {
    let mut v___x_3693_: u32 = 0;
    v___x_3693_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once),
        _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1,
    );
    return v___x_3693_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_Internal_getHardwareCurrency___boxed(
    mut v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_3695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3696_: u32 = 0;
    let mut v_r_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3696_ = lean_internal_get_hardware_concurrency(
        v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_3695_,
    );
    v_r_3697_ = crate::leanh::lean_box_uint32(v_res_3696_);
    return v_r_3697_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0() -> u32 {
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: u32 = 0;
    v___x_3698_ = crate::leanh::lean_box(0);
    v___x_3699_ = lean_internal_get_hardware_concurrency(v___x_3698_);
    return v___x_3699_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_defaultNumThreads() -> u32 {
    let mut v___x_3700_: u8 = 0;
    v___x_3700_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__36),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once),
        _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36,
    );
    if v___x_3700_ == 0 {
        let mut v___x_3701_: u32 = 0;
        v___x_3701_ = 0;
        return v___x_3701_;
    } else {
        let mut v___x_3702_: u32 = 0;
        v___x_3702_ = crate::leanh::lean_uint32_once(
            core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0),
            core::ptr::addr_of_mut!(
                l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once
            ),
            _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0,
        );
        return v___x_3702_;
    }
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3703_ = crate::leanh::lean_box(0);
    v___x_3704_ = lean_internal_get_default_options(v___x_3703_);
    return v___x_3704_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u32 = 0;
    let mut v___x_3709_: u32 = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: u8 = 0;
    let mut v___x_3712_: u8 = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3707_ = crate::leanh::lean_box(0);
    v___x_3708_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
    v___x_3709_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
    v___x_3710_ = l_Lean_Options_empty;
    v___x_3711_ = 0;
    v___x_3712_ = 0;
    v___x_3713_ = l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1;
    v___x_3714_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once),
        _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0,
    );
    v___x_3715_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
    crate::leanh::lean_ctor_set(v___x_3715_, 0, v___x_3714_);
    crate::leanh::lean_ctor_set(v___x_3715_, 1, v___x_3713_);
    crate::leanh::lean_ctor_set(v___x_3715_, 2, v___x_3710_);
    crate::leanh::lean_ctor_set(v___x_3715_, 3, v___x_3707_);
    crate::leanh::lean_ctor_set(v___x_3715_, 4, v___x_3707_);
    crate::leanh::lean_ctor_set(v___x_3715_, 5, v___x_3707_);
    crate::leanh::lean_ctor_set(v___x_3715_, 6, v___x_3707_);
    crate::leanh::lean_ctor_set(v___x_3715_, 7, v___x_3707_);
    crate::leanh::lean_ctor_set(v___x_3715_, 8, v___x_3707_);
    crate::leanh::lean_ctor_set(v___x_3715_, 9, v___x_3713_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
        v___x_3712_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint32(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
        v___x_3709_,
    );
    crate::leanh::lean_ctor_set_uint32(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
        v___x_3708_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
        v___x_3711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3715_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
        v___x_3711_,
    );
    return v___x_3715_;
}
pub unsafe fn lean_shell_options_mk(
    mut v_x_3716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once),
        _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2,
    );
    return v___x_3717_;
}
pub unsafe fn lean_shell_options_get_run(mut v_opts_3718_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_run_3719_: u8 = 0;
    v_run_3719_ = crate::leanh::lean_ctor_get_uint8(
        v_opts_3718_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
    );
    crate::leanh::lean_dec_ref(v_opts_3718_);
    return v_run_3719_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(
    mut v_opts_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3721_: u8 = 0;
    let mut v_r_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3721_ = lean_shell_options_get_run(v_opts_3720_);
    v_r_3722_ = crate::leanh::lean_box((v_res_3721_) as usize);
    return v_r_3722_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(
    mut v_opts_3723_: *mut crate::leanh::LeanObject,
    mut v_opt_3724_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3725_ = crate::leanh::lean_ctor_get(v_opt_3724_, 0);
    v_defValue_3726_ = crate::leanh::lean_ctor_get(v_opt_3724_, 1);
    v_map_3727_ = crate::leanh::lean_ctor_get(v_opts_3723_, 0);
    v___x_3728_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3727_,
            v_name_3725_,
        );
    if crate::leanh::lean_obj_tag(v___x_3728_) == 0 {
        let mut v___x_3729_: u8 = 0;
        v___x_3729_ = (crate::leanh::lean_unbox(v_defValue_3726_) as u8);
        return v___x_3729_;
    } else {
        let mut v_val_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3730_ = crate::leanh::lean_ctor_get(v___x_3728_, 0);
        crate::leanh::lean_inc(v_val_3730_);
        crate::leanh::lean_dec_ref_known(v___x_3728_, 1);
        if crate::leanh::lean_obj_tag(v_val_3730_) == 1 {
            let mut v_v_3731_: u8 = 0;
            v_v_3731_ = crate::leanh::lean_ctor_get_uint8(v_val_3730_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3730_, 0);
            return v_v_3731_;
        } else {
            let mut v___x_3732_: u8 = 0;
            crate::leanh::lean_dec(v_val_3730_);
            v___x_3732_ = (crate::leanh::lean_unbox(v_defValue_3726_) as u8);
            return v___x_3732_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(
    mut v_opts_3733_: *mut crate::leanh::LeanObject,
    mut v_opt_3734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3735_: u8 = 0;
    let mut v_r_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3735_ =
        l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(
            v_opts_3733_,
            v_opt_3734_,
        );
    crate::leanh::lean_dec_ref(v_opt_3734_);
    crate::leanh::lean_dec_ref(v_opts_3733_);
    v_r_3736_ = crate::leanh::lean_box((v_res_3735_) as usize);
    return v_r_3736_;
}
pub unsafe fn lean_shell_options_get_profiler(
    mut v_opts_3737_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_leanOpts_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    v_leanOpts_3738_ = crate::leanh::lean_ctor_get(v_opts_3737_, 0);
    crate::leanh::lean_inc_ref(v_leanOpts_3738_);
    crate::leanh::lean_dec_ref(v_opts_3737_);
    v___x_3739_ = l_Lean_profiler;
    v___x_3740_ =
        l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(
            v_leanOpts_3738_,
            v___x_3739_,
        );
    crate::leanh::lean_dec_ref(v_leanOpts_3738_);
    return v___x_3740_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(
    mut v_opts_3741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3742_: u8 = 0;
    let mut v_r_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3742_ = lean_shell_options_get_profiler(v_opts_3741_);
    v_r_3743_ = crate::leanh::lean_box((v_res_3742_) as usize);
    return v_r_3743_;
}
pub unsafe fn lean_shell_options_get_num_threads(
    mut v_opts_3744_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_numThreads_3745_: u32 = 0;
    v_numThreads_3745_ = crate::leanh::lean_ctor_get_uint32(
        v_opts_3744_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
    );
    crate::leanh::lean_dec_ref(v_opts_3744_);
    return v_numThreads_3745_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(
    mut v_opts_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3747_: u32 = 0;
    let mut v_r_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3747_ = lean_shell_options_get_num_threads(v_opts_3746_);
    v_r_3748_ = crate::leanh::lean_box_uint32(v_res_3747_);
    return v_r_3748_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_checkOptArg(
    mut v_optName_3751_: *mut crate::leanh::LeanObject,
    mut v_optArg_x3f_3752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_optArg_x3f_3752_) == 1 {
                    v_val_3754_ = crate::leanh::lean_ctor_get(v_optArg_x3f_3752_, 0);
                    v_isSharedCheck_3761_ =
                        (!crate::leanh::lean_is_exclusive(v_optArg_x3f_3752_)) as u8;
                    if v_isSharedCheck_3761_ == 0 {
                        v___x_3756_ = v_optArg_x3f_3752_;
                        v_isShared_3757_ = v_isSharedCheck_3761_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3754_);
                        crate::leanh::lean_dec(v_optArg_x3f_3752_);
                        v___x_3756_ = crate::leanh::lean_box(0);
                        v_isShared_3757_ = v_isSharedCheck_3761_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_optArg_x3f_3752_);
                    v___x_3762_ = l___private_Lean_Shell_0__Lean_checkOptArg___closed__0;
                    v___x_3763_ = lean_string_append(v___x_3762_, v_optName_3751_);
                    v___x_3764_ = l___private_Lean_Shell_0__Lean_checkOptArg___closed__1;
                    v___x_3765_ = lean_string_append(v___x_3763_, v___x_3764_);
                    v___x_3766_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3766_, 0, v___x_3765_);
                    v___x_3767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3767_, 0, v___x_3766_);
                    return v___x_3767_;
                }
            }
            1 => {
                if v_isShared_3757_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3756_, 0);
                    v___x_3759_ = v___x_3756_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3760_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_val_3754_);
                    v___x_3759_ = v_reuseFailAlloc_3760_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_checkOptArg___boxed(
    mut v_optName_3768_: *mut crate::leanh::LeanObject,
    mut v_optArg_x3f_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_3768_, v_optArg_x3f_3769_);
    crate::leanh::lean_dec_ref(v_optName_3768_);
    return v_res_3771_;
}
pub unsafe fn l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(
    mut v_o_3775_: *mut crate::leanh::LeanObject,
    mut v_k_3776_: *mut crate::leanh::LeanObject,
    mut v_v_3777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3779_: u8 = 0;
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3778_ = crate::leanh::lean_ctor_get(v_o_3775_, 0);
                v_hasTrace_3779_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_3775_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3793_ = (!crate::leanh::lean_is_exclusive(v_o_3775_)) as u8;
                if v_isSharedCheck_3793_ == 0 {
                    v___x_3781_ = v_o_3775_;
                    v_isShared_3782_ = v_isSharedCheck_3793_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_3778_);
                    crate::leanh::lean_dec(v_o_3775_);
                    v___x_3781_ = crate::leanh::lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3793_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3783_, 0, v_v_3777_);
                crate::leanh::lean_inc(v_k_3776_);
                v___x_3784_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3776_, v___x_3783_, v_map_3778_);
                if v_hasTrace_3779_ == 0 {
                    v___x_3785_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1;
                    v___x_3786_ = l_Lean_Name_isPrefixOf(v___x_3785_, v_k_3776_);
                    crate::leanh::lean_dec(v_k_3776_);
                    if v_isShared_3782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3781_, 0, v___x_3784_);
                        v___x_3788_ = v___x_3781_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3789_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3784_);
                        v___x_3788_ = v_reuseFailAlloc_3789_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3776_);
                    if v_isShared_3782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3781_, 0, v___x_3784_);
                        v___x_3791_ = v___x_3781_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3792_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3784_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3792_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3779_,
                        );
                        v___x_3791_ = v_reuseFailAlloc_3792_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3788_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3786_,
                );
                return v___x_3788_;
            }
            3 => {
                return v___x_3791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(
    mut v___x_3794_: *mut crate::leanh::LeanObject,
    mut v_arg_3795_: *mut crate::leanh::LeanObject,
    mut v_a_3796_: *mut crate::leanh::LeanObject,
    mut v_b_3797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    let mut v___x_3802_: u32 = 0;
    let mut v___x_3803_: u32 = 0;
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_3798_ = crate::leanh::lean_ctor_get(v___x_3794_, 1);
                v_endExclusive_3799_ = crate::leanh::lean_ctor_get(v___x_3794_, 2);
                v___x_3800_ = lean_nat_sub(v_endExclusive_3799_, v_startInclusive_3798_);
                v___x_3801_ = lean_nat_dec_eq(v_a_3796_, v___x_3800_);
                crate::leanh::lean_dec(v___x_3800_);
                if v___x_3801_ == 0 {
                    v___x_3802_ = lean_string_utf8_get_fast(v_arg_3795_, v_a_3796_);
                    v___x_3803_ = 61;
                    v___x_3804_ = lean_uint32_dec_eq(v___x_3802_, v___x_3803_);
                    if v___x_3804_ == 0 {
                        v___x_3805_ = crate::leanh::lean_box(0);
                        v___x_3806_ = lean_string_utf8_next_fast(v_arg_3795_, v_a_3796_);
                        crate::leanh::lean_dec(v_a_3796_);
                        v_a_3796_ = v___x_3806_;
                        v_b_3797_ = v___x_3805_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3808_, 0, v_a_3796_);
                        return v___x_3808_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3796_);
                    crate::leanh::lean_inc(v_b_3797_);
                    return v_b_3797_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(
    mut v___x_3809_: *mut crate::leanh::LeanObject,
    mut v_arg_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
    mut v_b_3812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3813_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_3809_, v_arg_3810_, v_a_3811_, v_b_3812_);
    crate::leanh::lean_dec(v_b_3812_);
    crate::leanh::lean_dec_ref(v_arg_3810_);
    crate::leanh::lean_dec_ref(v___x_3809_);
    return v_res_3813_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_setConfigOption(
    mut v_opts_3817_: *mut crate::leanh::LeanObject,
    mut v_arg_3818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut v_a_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_3852_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3853_ = lean_string_utf8_byte_size(v_arg_3818_);
                crate::leanh::lean_inc_ref(v_arg_3818_);
                v___x_3854_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3854_, 0, v_arg_3818_);
                crate::leanh::lean_ctor_set(v___x_3854_, 1, v_searcher_3852_);
                crate::leanh::lean_ctor_set(v___x_3854_, 2, v___x_3853_);
                v___x_3855_ = crate::leanh::lean_box(0);
                v___x_3856_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_3854_, v_arg_3818_, v_searcher_3852_, v___x_3855_);
                crate::leanh::lean_dec_ref_known(v___x_3854_, 3);
                if crate::leanh::lean_obj_tag(v___x_3856_) == 0 {
                    v___y_3821_ = v___x_3853_;
                    state = 1;
                    continue;
                } else {
                    v_val_3857_ = crate::leanh::lean_ctor_get(v___x_3856_, 0);
                    crate::leanh::lean_inc(v_val_3857_);
                    crate::leanh::lean_dec_ref_known(v___x_3856_, 1);
                    v___y_3821_ = v_val_3857_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3822_ = lean_string_utf8_byte_size(v_arg_3818_);
                v___x_3823_ = lean_nat_dec_eq(v___y_3821_, v___x_3822_);
                if v___x_3823_ == 0 {
                    v___x_3824_ = l_Lean_getOptionDecls();
                    if crate::leanh::lean_obj_tag(v___x_3824_) == 0 {
                        v_a_3825_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
                        v_isSharedCheck_3841_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3824_)) as u8;
                        if v_isSharedCheck_3841_ == 0 {
                            v___x_3827_ = v___x_3824_;
                            v_isShared_3828_ = v_isSharedCheck_3841_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3825_);
                            crate::leanh::lean_dec(v___x_3824_);
                            v___x_3827_ = crate::leanh::lean_box(0);
                            v_isShared_3828_ = v_isSharedCheck_3841_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3821_);
                        crate::leanh::lean_dec_ref(v_arg_3818_);
                        crate::leanh::lean_dec_ref(v_opts_3817_);
                        v_a_3842_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
                        v_isSharedCheck_3849_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3824_)) as u8;
                        if v_isSharedCheck_3849_ == 0 {
                            v___x_3844_ = v___x_3824_;
                            v_isShared_3845_ = v_isSharedCheck_3849_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3842_);
                            crate::leanh::lean_dec(v___x_3824_);
                            v___x_3844_ = crate::leanh::lean_box(0);
                            v_isShared_3845_ = v_isSharedCheck_3849_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3821_);
                    crate::leanh::lean_dec_ref(v_arg_3818_);
                    crate::leanh::lean_dec_ref(v_opts_3817_);
                    v___x_3850_ = l___private_Lean_Shell_0__Lean_setConfigOption___closed__1;
                    v___x_3851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3851_, 0, v___x_3850_);
                    return v___x_3851_;
                }
            }
            2 => {
                v___x_3829_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc(v___y_3821_);
                crate::leanh::lean_inc_ref(v_arg_3818_);
                v___x_3830_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3830_, 0, v_arg_3818_);
                crate::leanh::lean_ctor_set(v___x_3830_, 1, v___x_3829_);
                crate::leanh::lean_ctor_set(v___x_3830_, 2, v___y_3821_);
                v___x_3831_ = lean_string_utf8_next_fast(v_arg_3818_, v___y_3821_);
                crate::leanh::lean_dec(v___y_3821_);
                v_name_3832_ = l_String_Slice_toName(v___x_3830_);
                crate::leanh::lean_dec_ref_known(v___x_3830_, 3);
                v_val_3833_ = lean_string_utf8_extract(v_arg_3818_, v___x_3831_, v___x_3822_);
                crate::leanh::lean_dec_ref(v_arg_3818_);
                v___x_3834_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3825_, v_name_3832_);
                crate::leanh::lean_dec(v_a_3825_);
                if crate::leanh::lean_obj_tag(v___x_3834_) == 1 {
                    crate::leanh::lean_del_object(v___x_3827_);
                    v_val_3835_ = crate::leanh::lean_ctor_get(v___x_3834_, 0);
                    crate::leanh::lean_inc(v_val_3835_);
                    crate::leanh::lean_dec_ref_known(v___x_3834_, 1);
                    v___x_3836_ = l_Lean_Language_Lean_setOption(
                        v_opts_3817_,
                        v_val_3835_,
                        v_name_3832_,
                        v_val_3833_,
                    );
                    return v___x_3836_;
                } else {
                    crate::leanh::lean_dec(v___x_3834_);
                    v___x_3837_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_3817_, v_name_3832_, v_val_3833_);
                    if v_isShared_3828_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3827_, 0, v___x_3837_);
                        v___x_3839_ = v___x_3827_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
                        v___x_3839_ = v_reuseFailAlloc_3840_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3839_;
            }
            4 => {
                if v_isShared_3845_ == 0 {
                    v___x_3847_ = v___x_3844_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
                    v___x_3847_ = v_reuseFailAlloc_3848_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_setConfigOption___boxed(
    mut v_opts_3858_: *mut crate::leanh::LeanObject,
    mut v_arg_3859_: *mut crate::leanh::LeanObject,
    mut v_a_3860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3861_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_3858_, v_arg_3859_);
    return v_res_3861_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(
    mut v___x_3862_: *mut crate::leanh::LeanObject,
    mut v_arg_3863_: *mut crate::leanh::LeanObject,
    mut v_inst_3864_: *mut crate::leanh::LeanObject,
    mut v_R_3865_: *mut crate::leanh::LeanObject,
    mut v_a_3866_: *mut crate::leanh::LeanObject,
    mut v_b_3867_: *mut crate::leanh::LeanObject,
    mut v_c_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_3862_, v_arg_3863_, v_a_3866_, v_b_3867_);
    return v___x_3869_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(
    mut v___x_3870_: *mut crate::leanh::LeanObject,
    mut v_arg_3871_: *mut crate::leanh::LeanObject,
    mut v_inst_3872_: *mut crate::leanh::LeanObject,
    mut v_R_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_b_3875_: *mut crate::leanh::LeanObject,
    mut v_c_3876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3877_ =
        l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(
            v___x_3870_,
            v_arg_3871_,
            v_inst_3872_,
            v_R_3873_,
            v_a_3874_,
            v_b_3875_,
            v_c_3876_,
        );
    crate::leanh::lean_dec(v_b_3875_);
    crate::leanh::lean_dec_ref(v_arg_3871_);
    crate::leanh::lean_dec_ref(v___x_3870_);
    return v_res_3877_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(
    mut v_msg_3879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v_unused_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3881_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                v___x_3882_ = l_IO_eprint___redArg(v___f_3881_, v_msg_3879_);
                if crate::leanh::lean_obj_tag(v___x_3882_) == 0 {
                    v_a_3883_ = crate::leanh::lean_ctor_get(v___x_3882_, 0);
                    v_isSharedCheck_3890_ = (!crate::leanh::lean_is_exclusive(v___x_3882_)) as u8;
                    if v_isSharedCheck_3890_ == 0 {
                        v___x_3885_ = v___x_3882_;
                        v_isShared_3886_ = v_isSharedCheck_3890_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3883_);
                        crate::leanh::lean_dec(v___x_3882_);
                        v___x_3885_ = crate::leanh::lean_box(0);
                        v_isShared_3886_ = v_isSharedCheck_3890_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3898_ = (!crate::leanh::lean_is_exclusive(v___x_3882_)) as u8;
                    if v_isSharedCheck_3898_ == 0 {
                        v_unused_3899_ = crate::leanh::lean_ctor_get(v___x_3882_, 0);
                        crate::leanh::lean_dec(v_unused_3899_);
                        v___x_3892_ = v___x_3882_;
                        v_isShared_3893_ = v_isSharedCheck_3898_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3882_);
                        v___x_3892_ = crate::leanh::lean_box(0);
                        v_isShared_3893_ = v_isSharedCheck_3898_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3886_ == 0 {
                    v___x_3888_ = v___x_3885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
                    v___x_3888_ = v_reuseFailAlloc_3889_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3888_;
            }
            3 => {
                v___x_3894_ = crate::leanh::lean_box(0);
                if v_isShared_3893_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3892_, 0);
                    crate::leanh::lean_ctor_set(v___x_3892_, 0, v___x_3894_);
                    v___x_3896_ = v___x_3892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
                    v___x_3896_ = v_reuseFailAlloc_3897_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(
    mut v_msg_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3902_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_3900_);
    return v_res_3902_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3905_: u32 = 0;
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3905_ = 1;
    v___x_3906_ = crate::leanh::lean_box_uint32(v___x_3905_);
    return v___x_3906_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(
    mut v_x_3907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3916_ = crate::leanh::lean_apply_1(v_x_3907_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_3916_) == 0 {
                    v_a_3917_ = crate::leanh::lean_ctor_get(v___x_3916_, 0);
                    v_isSharedCheck_3924_ = (!crate::leanh::lean_is_exclusive(v___x_3916_)) as u8;
                    if v_isSharedCheck_3924_ == 0 {
                        v___x_3919_ = v___x_3916_;
                        v_isShared_3920_ = v_isSharedCheck_3924_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3917_);
                        crate::leanh::lean_dec(v___x_3916_);
                        v___x_3919_ = crate::leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3924_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3925_ = crate::leanh::lean_ctor_get(v___x_3916_, 0);
                    crate::leanh::lean_inc(v_a_3925_);
                    crate::leanh::lean_dec_ref_known(v___x_3916_, 1);
                    v___x_3930_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                    v___f_3931_ =
                        l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                    v___x_3932_ = l_IO_eprint___redArg(v___f_3931_, v___x_3930_);
                    crate::leanh::lean_dec_ref(v___x_3932_);
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_3910_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_3911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3911_, 0, v___x_3910_);
                return v___x_3911_;
            }
            2 => {
                v___x_3913_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___f_3914_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                v___x_3915_ = l_IO_eprint___redArg(v___f_3914_, v___x_3913_);
                crate::leanh::lean_dec_ref(v___x_3915_);
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3922_;
            }
            5 => {
                v___x_3927_ = lean_io_error_to_string(v_a_3925_);
                v___f_3928_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                v___x_3929_ = l_IO_eprint___redArg(v___f_3928_, v___x_3927_);
                crate::leanh::lean_dec_ref(v___x_3929_);
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(
    mut v_x_3933_: *mut crate::leanh::LeanObject,
    mut v_a_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_3933_);
    return v_res_3935_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(
    mut v_00_u03b1_3936_: *mut crate::leanh::LeanObject,
    mut v_x_3937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_a_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3946_ = crate::leanh::lean_apply_1(v_x_3937_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_3946_) == 0 {
                    v_a_3947_ = crate::leanh::lean_ctor_get(v___x_3946_, 0);
                    v_isSharedCheck_3954_ = (!crate::leanh::lean_is_exclusive(v___x_3946_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3949_ = v___x_3946_;
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3947_);
                        crate::leanh::lean_dec(v___x_3946_);
                        v___x_3949_ = crate::leanh::lean_box(0);
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3955_ = crate::leanh::lean_ctor_get(v___x_3946_, 0);
                    crate::leanh::lean_inc(v_a_3955_);
                    crate::leanh::lean_dec_ref_known(v___x_3946_, 1);
                    v___x_3960_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                    v___f_3961_ =
                        l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                    v___x_3962_ = l_IO_eprint___redArg(v___f_3961_, v___x_3960_);
                    crate::leanh::lean_dec_ref(v___x_3962_);
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_3940_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_3941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3941_, 0, v___x_3940_);
                return v___x_3941_;
            }
            2 => {
                v___x_3943_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___f_3944_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                v___x_3945_ = l_IO_eprint___redArg(v___f_3944_, v___x_3943_);
                crate::leanh::lean_dec_ref(v___x_3945_);
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_3950_ == 0 {
                    v___x_3952_ = v___x_3949_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3952_;
            }
            5 => {
                v___x_3957_ = lean_io_error_to_string(v_a_3955_);
                v___f_3958_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                v___x_3959_ = l_IO_eprint___redArg(v___f_3958_, v___x_3957_);
                crate::leanh::lean_dec_ref(v___x_3959_);
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(
    mut v_00_u03b1_3963_: *mut crate::leanh::LeanObject,
    mut v_x_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3966_ =
        l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_3963_, v_x_3964_);
    return v_res_3966_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(
    mut v_opt_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3974_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0;
                v___x_3975_ = lean_string_append(v___x_3974_, v_opt_3969_);
                v___x_3976_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1;
                v___x_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
                v___f_3978_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                v___x_3979_ = l_IO_eprint___redArg(v___f_3978_, v___x_3977_);
                crate::leanh::lean_dec_ref(v___x_3979_);
                state = 1;
                continue;
            }
            1 => {
                v___x_3972_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_3973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3973_, 0, v___x_3972_);
                return v___x_3973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(
    mut v_opt_3980_: *mut crate::leanh::LeanObject,
    mut v_a_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3982_ =
        l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_3980_);
    crate::leanh::lean_dec_ref(v_opt_3980_);
    return v_res_3982_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(
    mut v_opt_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3990_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0;
                v___x_3991_ = lean_string_append(v___x_3990_, v_opt_3985_);
                v___x_3992_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1;
                v___x_3993_ = lean_string_append(v___x_3991_, v___x_3992_);
                v___f_3994_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0;
                v___x_3995_ = l_IO_eprint___redArg(v___f_3994_, v___x_3993_);
                crate::leanh::lean_dec_ref(v___x_3995_);
                state = 1;
                continue;
            }
            1 => {
                v___x_3988_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_3989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3989_, 0, v___x_3988_);
                return v___x_3989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(
    mut v_opt_3996_: *mut crate::leanh::LeanObject,
    mut v_a_3997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3998_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_3996_);
    crate::leanh::lean_dec_ref(v_opt_3996_);
    return v_res_3998_;
}
pub unsafe fn l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
    mut v_s_3999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4001_ = lean_get_stderr();
    v_putStr_4002_ = crate::leanh::lean_ctor_get(v___x_4001_, 4);
    crate::leanh::lean_inc_ref(v_putStr_4002_);
    crate::leanh::lean_dec_ref(v___x_4001_);
    v___x_4003_ = crate::leanh::lean_apply_2(v_putStr_4002_, v_s_3999_, crate::leanh::lean_box(0));
    return v___x_4003_;
}
pub unsafe fn l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(
    mut v_s_4004_: *mut crate::leanh::LeanObject,
    mut v_a_4005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4006_ =
        l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_4004_);
    return v_res_4006_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__4(
    mut v_o_4007_: *mut crate::leanh::LeanObject,
    mut v_k_4008_: *mut crate::leanh::LeanObject,
    mut v_v_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4011_: u8 = 0;
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: u8 = 0;
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4010_ = crate::leanh::lean_ctor_get(v_o_4007_, 0);
                v_hasTrace_4011_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_4007_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4025_ = (!crate::leanh::lean_is_exclusive(v_o_4007_)) as u8;
                if v_isSharedCheck_4025_ == 0 {
                    v___x_4013_ = v_o_4007_;
                    v_isShared_4014_ = v_isSharedCheck_4025_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_4010_);
                    crate::leanh::lean_dec(v_o_4007_);
                    v___x_4013_ = crate::leanh::lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4015_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4015_, 0, v_v_4009_);
                crate::leanh::lean_inc(v_k_4008_);
                v___x_4016_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4008_, v___x_4015_, v_map_4010_);
                if v_hasTrace_4011_ == 0 {
                    v___x_4017_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1;
                    v___x_4018_ = l_Lean_Name_isPrefixOf(v___x_4017_, v_k_4008_);
                    crate::leanh::lean_dec(v_k_4008_);
                    if v_isShared_4014_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_4016_);
                        v___x_4020_ = v___x_4013_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4021_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4016_);
                        v___x_4020_ = v_reuseFailAlloc_4021_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4008_);
                    if v_isShared_4014_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_4016_);
                        v___x_4023_ = v___x_4013_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4024_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_4016_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4024_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4011_,
                        );
                        v___x_4023_ = v_reuseFailAlloc_4024_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4020_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4018_,
                );
                return v___x_4020_;
            }
            3 => {
                return v___x_4023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(
    mut v_opts_4026_: *mut crate::leanh::LeanObject,
    mut v_opt_4027_: *mut crate::leanh::LeanObject,
    mut v_val_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4029_ = crate::leanh::lean_ctor_get(v_opt_4027_, 0);
    crate::leanh::lean_inc(v_name_4029_);
    crate::leanh::lean_dec_ref(v_opt_4027_);
    v___x_4030_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__4(v_opts_4026_, v_name_4029_, v_val_4028_);
    return v___x_4030_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(
    mut v_s_4031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4033_ = lean_get_stdout();
    v_putStr_4034_ = crate::leanh::lean_ctor_get(v___x_4033_, 4);
    crate::leanh::lean_inc_ref(v_putStr_4034_);
    crate::leanh::lean_dec_ref(v___x_4033_);
    v___x_4035_ = crate::leanh::lean_apply_2(v_putStr_4034_, v_s_4031_, crate::leanh::lean_box(0));
    return v___x_4035_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6___boxed(
    mut v_s_4036_: *mut crate::leanh::LeanObject,
    mut v_a_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4038_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(v_s_4036_);
    return v_res_4038_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(
    mut v_s_4039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4041_: u32 = 0;
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = 10;
    v___x_4042_ = lean_string_push(v_s_4039_, v___x_4041_);
    v___x_4043_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(v___x_4042_);
    return v___x_4043_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4___boxed(
    mut v_s_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ =
        l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v_s_4044_);
    return v_res_4046_;
}
pub unsafe fn l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(
    mut v_s_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4049_: u32 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4049_ = 10;
    v___x_4050_ = lean_string_push(v_s_4047_, v___x_4049_);
    v___x_4051_ =
        l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4050_);
    return v___x_4051_;
}
pub unsafe fn l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(
    mut v_s_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4054_ =
        l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_s_4052_);
    return v_res_4054_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2(
    mut v_o_4055_: *mut crate::leanh::LeanObject,
    mut v_k_4056_: *mut crate::leanh::LeanObject,
    mut v_v_4057_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4059_: u8 = 0;
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4058_ = crate::leanh::lean_ctor_get(v_o_4055_, 0);
                v_hasTrace_4059_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_4055_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4073_ = (!crate::leanh::lean_is_exclusive(v_o_4055_)) as u8;
                if v_isSharedCheck_4073_ == 0 {
                    v___x_4061_ = v_o_4055_;
                    v_isShared_4062_ = v_isSharedCheck_4073_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_4058_);
                    crate::leanh::lean_dec(v_o_4055_);
                    v___x_4061_ = crate::leanh::lean_box(0);
                    v_isShared_4062_ = v_isSharedCheck_4073_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4063_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_4063_, 0 as u32, v_v_4057_);
                crate::leanh::lean_inc(v_k_4056_);
                v___x_4064_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4056_, v___x_4063_, v_map_4058_);
                if v_hasTrace_4059_ == 0 {
                    v___x_4065_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1;
                    v___x_4066_ = l_Lean_Name_isPrefixOf(v___x_4065_, v_k_4056_);
                    crate::leanh::lean_dec(v_k_4056_);
                    if v_isShared_4062_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4061_, 0, v___x_4064_);
                        v___x_4068_ = v___x_4061_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4064_);
                        v___x_4068_ = v_reuseFailAlloc_4069_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4056_);
                    if v_isShared_4062_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4061_, 0, v___x_4064_);
                        v___x_4071_ = v___x_4061_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4072_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4064_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4072_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4059_,
                        );
                        v___x_4071_ = v_reuseFailAlloc_4072_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4068_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4066_,
                );
                return v___x_4068_;
            }
            3 => {
                return v___x_4071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2___boxed(
    mut v_o_4074_: *mut crate::leanh::LeanObject,
    mut v_k_4075_: *mut crate::leanh::LeanObject,
    mut v_v_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_4077_: u8 = 0;
    let mut v_res_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_4077_ = (crate::leanh::lean_unbox(v_v_4076_) as u8);
    v_res_4078_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2(v_o_4074_, v_k_4075_, v_v_boxed_4077_);
    return v_res_4078_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(
    mut v_opts_4079_: *mut crate::leanh::LeanObject,
    mut v_opt_4080_: *mut crate::leanh::LeanObject,
    mut v_val_4081_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4082_ = crate::leanh::lean_ctor_get(v_opt_4080_, 0);
    crate::leanh::lean_inc(v_name_4082_);
    crate::leanh::lean_dec_ref(v_opt_4080_);
    v___x_4083_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2(v_opts_4079_, v_name_4082_, v_val_4081_);
    return v___x_4083_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2___boxed(
    mut v_opts_4084_: *mut crate::leanh::LeanObject,
    mut v_opt_4085_: *mut crate::leanh::LeanObject,
    mut v_val_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_4087_: u8 = 0;
    let mut v_res_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4087_ = (crate::leanh::lean_unbox(v_val_4086_) as u8);
    v_res_4088_ =
        l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(
            v_opts_4084_,
            v_opt_4085_,
            v_val_boxed_4087_,
        );
    return v_res_4088_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = l_System_Platform_numBits;
    v___x_4115_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4116_ = lean_nat_pow(v___x_4115_, v___x_4114_);
    return v___x_4116_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4126_: u32 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4126_ = 0;
    v___x_4127_ = crate::leanh::lean_box_uint32(v___x_4126_);
    return v___x_4127_;
}
pub unsafe fn lean_shell_options_process(
    mut v_opts_4128_: *mut crate::leanh::LeanObject,
    mut v_opt_4129_: u32,
    mut v_optArg_x3f_4130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4240_: u8 = 0;
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v_unused_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: u32 = 0;
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: u32 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: u32 = 0;
    let mut v___x_4333_: u8 = 0;
    let mut v___x_4334_: u32 = 0;
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: u32 = 0;
    let mut v___x_4337_: u8 = 0;
    let mut v___x_4338_: u32 = 0;
    let mut v___x_4339_: u8 = 0;
    let mut v___x_4340_: u32 = 0;
    let mut v___x_4341_: u8 = 0;
    let mut v___x_4342_: u32 = 0;
    let mut v___x_4343_: u8 = 0;
    let mut v___x_4344_: u32 = 0;
    let mut v___x_4345_: u8 = 0;
    let mut v___x_4346_: u32 = 0;
    let mut v___x_4347_: u8 = 0;
    let mut v___x_4348_: u32 = 0;
    let mut v___x_4349_: u8 = 0;
    let mut v___x_4350_: u32 = 0;
    let mut v___x_4351_: u8 = 0;
    let mut v___x_4352_: u32 = 0;
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: u32 = 0;
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4356_: u32 = 0;
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: u32 = 0;
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: u32 = 0;
    let mut v___x_4361_: u8 = 0;
    let mut v___x_4362_: u32 = 0;
    let mut v___x_4363_: u8 = 0;
    let mut v___x_4364_: u32 = 0;
    let mut v___x_4365_: u8 = 0;
    let mut v___x_4366_: u32 = 0;
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: u32 = 0;
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: u32 = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: u32 = 0;
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: u32 = 0;
    let mut v___x_4375_: u8 = 0;
    let mut v___x_4376_: u32 = 0;
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: u32 = 0;
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: u32 = 0;
    let mut v___x_4381_: u8 = 0;
    let mut v___x_4382_: u32 = 0;
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4384_: u32 = 0;
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: u32 = 0;
    let mut v___x_4387_: u8 = 0;
    let mut v___x_4388_: u32 = 0;
    let mut v___x_4389_: u8 = 0;
    let mut v___x_4390_: u32 = 0;
    let mut v___x_4391_: u8 = 0;
    let mut v___x_4392_: u32 = 0;
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: u32 = 0;
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4396_: u32 = 0;
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v_leanOpts_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4406_: u8 = 0;
    let mut v_printPrefix_4407_: u8 = 0;
    let mut v_printLibDir_4408_: u8 = 0;
    let mut v_useStdin_4409_: u8 = 0;
    let mut v_onlyDeps_4410_: u8 = 0;
    let mut v_onlySrcDeps_4411_: u8 = 0;
    let mut v_depsJson_4412_: u8 = 0;
    let mut v_opts_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4414_: u32 = 0;
    let mut v_numThreads_4415_: u32 = 0;
    let mut v_rootDir_x3f_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4422_: u8 = 0;
    let mut v_errorOnKinds_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4424_: u8 = 0;
    let mut v_run_4425_: u8 = 0;
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut v_isSharedCheck_4438_: u8 = 0;
    let mut v_a_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4450_: u8 = 0;
    let mut v_leanOpts_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4453_: u8 = 0;
    let mut v_printPrefix_4454_: u8 = 0;
    let mut v_printLibDir_4455_: u8 = 0;
    let mut v_useStdin_4456_: u8 = 0;
    let mut v_onlyDeps_4457_: u8 = 0;
    let mut v_onlySrcDeps_4458_: u8 = 0;
    let mut v_depsJson_4459_: u8 = 0;
    let mut v_opts_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4461_: u32 = 0;
    let mut v_numThreads_4462_: u32 = 0;
    let mut v_rootDir_x3f_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4468_: u8 = 0;
    let mut v_errorOnKinds_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4470_: u8 = 0;
    let mut v_run_4471_: u8 = 0;
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4482_: u8 = 0;
    let mut v_unused_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_a_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4497_: u8 = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_unused_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4522_: u8 = 0;
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4527_: u8 = 0;
    let mut v_unused_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4552_: u8 = 0;
    let mut v_a_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4561_: u8 = 0;
    let mut v_printPrefix_4562_: u8 = 0;
    let mut v_printLibDir_4563_: u8 = 0;
    let mut v_useStdin_4564_: u8 = 0;
    let mut v_onlyDeps_4565_: u8 = 0;
    let mut v_onlySrcDeps_4566_: u8 = 0;
    let mut v_depsJson_4567_: u8 = 0;
    let mut v_opts_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4569_: u32 = 0;
    let mut v_numThreads_4570_: u32 = 0;
    let mut v_rootDir_x3f_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4577_: u8 = 0;
    let mut v_errorOnKinds_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4579_: u8 = 0;
    let mut v_run_4580_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4590_: u8 = 0;
    let mut v_leanOpts_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printPrefix_4593_: u8 = 0;
    let mut v_printLibDir_4594_: u8 = 0;
    let mut v_useStdin_4595_: u8 = 0;
    let mut v_onlyDeps_4596_: u8 = 0;
    let mut v_onlySrcDeps_4597_: u8 = 0;
    let mut v_depsJson_4598_: u8 = 0;
    let mut v_opts_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4600_: u32 = 0;
    let mut v_numThreads_4601_: u32 = 0;
    let mut v_rootDir_x3f_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4608_: u8 = 0;
    let mut v_errorOnKinds_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4610_: u8 = 0;
    let mut v_run_4611_: u8 = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4620_: u8 = 0;
    let mut v_leanOpts_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printPrefix_4623_: u8 = 0;
    let mut v_printLibDir_4624_: u8 = 0;
    let mut v_useStdin_4625_: u8 = 0;
    let mut v_onlyDeps_4626_: u8 = 0;
    let mut v_onlySrcDeps_4627_: u8 = 0;
    let mut v_depsJson_4628_: u8 = 0;
    let mut v_opts_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4630_: u32 = 0;
    let mut v_numThreads_4631_: u32 = 0;
    let mut v_rootDir_x3f_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4638_: u8 = 0;
    let mut v_errorOnKinds_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4640_: u8 = 0;
    let mut v_run_4641_: u8 = 0;
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4644_: u8 = 0;
    let mut v___x_4645_: u8 = 0;
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4650_: u8 = 0;
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4656_: u8 = 0;
    let mut v_printPrefix_4657_: u8 = 0;
    let mut v_printLibDir_4658_: u8 = 0;
    let mut v_useStdin_4659_: u8 = 0;
    let mut v_onlyDeps_4660_: u8 = 0;
    let mut v_onlySrcDeps_4661_: u8 = 0;
    let mut v_depsJson_4662_: u8 = 0;
    let mut v_opts_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4664_: u32 = 0;
    let mut v_numThreads_4665_: u32 = 0;
    let mut v_rootDir_x3f_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4672_: u8 = 0;
    let mut v_errorOnKinds_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4674_: u8 = 0;
    let mut v_run_4675_: u8 = 0;
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4678_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4683_: u8 = 0;
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4693_: u8 = 0;
    let mut v_a_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut v_a_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4709_: u8 = 0;
    let mut v_printPrefix_4710_: u8 = 0;
    let mut v_useStdin_4711_: u8 = 0;
    let mut v_onlyDeps_4712_: u8 = 0;
    let mut v_onlySrcDeps_4713_: u8 = 0;
    let mut v_depsJson_4714_: u8 = 0;
    let mut v_opts_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4716_: u32 = 0;
    let mut v_numThreads_4717_: u32 = 0;
    let mut v_rootDir_x3f_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4724_: u8 = 0;
    let mut v_errorOnKinds_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4726_: u8 = 0;
    let mut v_run_4727_: u8 = 0;
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4730_: u8 = 0;
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4735_: u8 = 0;
    let mut v_leanOpts_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4738_: u8 = 0;
    let mut v_printLibDir_4739_: u8 = 0;
    let mut v_useStdin_4740_: u8 = 0;
    let mut v_onlyDeps_4741_: u8 = 0;
    let mut v_onlySrcDeps_4742_: u8 = 0;
    let mut v_depsJson_4743_: u8 = 0;
    let mut v_opts_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4745_: u32 = 0;
    let mut v_numThreads_4746_: u32 = 0;
    let mut v_rootDir_x3f_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4753_: u8 = 0;
    let mut v_errorOnKinds_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4755_: u8 = 0;
    let mut v_run_4756_: u8 = 0;
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4764_: u8 = 0;
    let mut v_leanOpts_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4767_: u8 = 0;
    let mut v_printPrefix_4768_: u8 = 0;
    let mut v_printLibDir_4769_: u8 = 0;
    let mut v_useStdin_4770_: u8 = 0;
    let mut v_onlyDeps_4771_: u8 = 0;
    let mut v_onlySrcDeps_4772_: u8 = 0;
    let mut v_depsJson_4773_: u8 = 0;
    let mut v_opts_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4775_: u32 = 0;
    let mut v_numThreads_4776_: u32 = 0;
    let mut v_rootDir_x3f_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4783_: u8 = 0;
    let mut v_errorOnKinds_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_4785_: u8 = 0;
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4788_: u8 = 0;
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4793_: u8 = 0;
    let mut v_leanOpts_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4796_: u8 = 0;
    let mut v_printPrefix_4797_: u8 = 0;
    let mut v_printLibDir_4798_: u8 = 0;
    let mut v_useStdin_4799_: u8 = 0;
    let mut v_onlyDeps_4800_: u8 = 0;
    let mut v_onlySrcDeps_4801_: u8 = 0;
    let mut v_depsJson_4802_: u8 = 0;
    let mut v_opts_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4804_: u32 = 0;
    let mut v_numThreads_4805_: u32 = 0;
    let mut v_rootDir_x3f_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorOnKinds_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4813_: u8 = 0;
    let mut v_run_4814_: u8 = 0;
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4817_: u8 = 0;
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4822_: u8 = 0;
    let mut v_leanOpts_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4825_: u8 = 0;
    let mut v_printPrefix_4826_: u8 = 0;
    let mut v_printLibDir_4827_: u8 = 0;
    let mut v_useStdin_4828_: u8 = 0;
    let mut v_onlySrcDeps_4829_: u8 = 0;
    let mut v_opts_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4831_: u32 = 0;
    let mut v_numThreads_4832_: u32 = 0;
    let mut v_rootDir_x3f_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4839_: u8 = 0;
    let mut v_errorOnKinds_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4841_: u8 = 0;
    let mut v_run_4842_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4845_: u8 = 0;
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4850_: u8 = 0;
    let mut v_leanOpts_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4853_: u8 = 0;
    let mut v_printPrefix_4854_: u8 = 0;
    let mut v_printLibDir_4855_: u8 = 0;
    let mut v_useStdin_4856_: u8 = 0;
    let mut v_onlyDeps_4857_: u8 = 0;
    let mut v_depsJson_4858_: u8 = 0;
    let mut v_opts_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4860_: u32 = 0;
    let mut v_numThreads_4861_: u32 = 0;
    let mut v_rootDir_x3f_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4868_: u8 = 0;
    let mut v_errorOnKinds_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4870_: u8 = 0;
    let mut v_run_4871_: u8 = 0;
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_leanOpts_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4882_: u8 = 0;
    let mut v_printPrefix_4883_: u8 = 0;
    let mut v_printLibDir_4884_: u8 = 0;
    let mut v_useStdin_4885_: u8 = 0;
    let mut v_onlySrcDeps_4886_: u8 = 0;
    let mut v_depsJson_4887_: u8 = 0;
    let mut v_opts_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4889_: u32 = 0;
    let mut v_numThreads_4890_: u32 = 0;
    let mut v_rootDir_x3f_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4897_: u8 = 0;
    let mut v_errorOnKinds_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4899_: u8 = 0;
    let mut v_run_4900_: u8 = 0;
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4903_: u8 = 0;
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut v_leanOpts_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4911_: u8 = 0;
    let mut v_printPrefix_4912_: u8 = 0;
    let mut v_printLibDir_4913_: u8 = 0;
    let mut v_useStdin_4914_: u8 = 0;
    let mut v_onlyDeps_4915_: u8 = 0;
    let mut v_onlySrcDeps_4916_: u8 = 0;
    let mut v_depsJson_4917_: u8 = 0;
    let mut v_opts_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_4919_: u32 = 0;
    let mut v_numThreads_4920_: u32 = 0;
    let mut v_rootDir_x3f_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4927_: u8 = 0;
    let mut v_errorOnKinds_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4929_: u8 = 0;
    let mut v_run_4930_: u8 = 0;
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4940_: u8 = 0;
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: u8 = 0;
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_4958_: u8 = 0;
    let mut v_printPrefix_4959_: u8 = 0;
    let mut v_printLibDir_4960_: u8 = 0;
    let mut v_useStdin_4961_: u8 = 0;
    let mut v_onlyDeps_4962_: u8 = 0;
    let mut v_onlySrcDeps_4963_: u8 = 0;
    let mut v_depsJson_4964_: u8 = 0;
    let mut v_opts_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numThreads_4966_: u32 = 0;
    let mut v_rootDir_x3f_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_4973_: u8 = 0;
    let mut v_errorOnKinds_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_4975_: u8 = 0;
    let mut v_run_4976_: u8 = 0;
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v___x_4980_: u32 = 0;
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4990_: u8 = 0;
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut v_a_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5005_: u8 = 0;
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5013_: u8 = 0;
    let mut v_printPrefix_5014_: u8 = 0;
    let mut v_printLibDir_5015_: u8 = 0;
    let mut v_useStdin_5016_: u8 = 0;
    let mut v_onlyDeps_5017_: u8 = 0;
    let mut v_onlySrcDeps_5018_: u8 = 0;
    let mut v_depsJson_5019_: u8 = 0;
    let mut v_opts_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5021_: u32 = 0;
    let mut v_numThreads_5022_: u32 = 0;
    let mut v_rootDir_x3f_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5029_: u8 = 0;
    let mut v_errorOnKinds_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5031_: u8 = 0;
    let mut v_run_5032_: u8 = 0;
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5047_: u8 = 0;
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5050_: u8 = 0;
    let mut v_a_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5062_: u8 = 0;
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5070_: u8 = 0;
    let mut v_printPrefix_5071_: u8 = 0;
    let mut v_printLibDir_5072_: u8 = 0;
    let mut v_useStdin_5073_: u8 = 0;
    let mut v_onlyDeps_5074_: u8 = 0;
    let mut v_onlySrcDeps_5075_: u8 = 0;
    let mut v_depsJson_5076_: u8 = 0;
    let mut v_opts_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5078_: u32 = 0;
    let mut v_numThreads_5079_: u32 = 0;
    let mut v_rootDir_x3f_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5086_: u8 = 0;
    let mut v_errorOnKinds_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5088_: u8 = 0;
    let mut v_run_5089_: u8 = 0;
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5104_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_a_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5119_: u8 = 0;
    let mut v_leanOpts_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5122_: u8 = 0;
    let mut v_printPrefix_5123_: u8 = 0;
    let mut v_printLibDir_5124_: u8 = 0;
    let mut v_useStdin_5125_: u8 = 0;
    let mut v_onlyDeps_5126_: u8 = 0;
    let mut v_onlySrcDeps_5127_: u8 = 0;
    let mut v_depsJson_5128_: u8 = 0;
    let mut v_opts_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5130_: u32 = 0;
    let mut v_numThreads_5131_: u32 = 0;
    let mut v_setupFileName_x3f_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5137_: u8 = 0;
    let mut v_errorOnKinds_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5139_: u8 = 0;
    let mut v_run_5140_: u8 = 0;
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5154_: u8 = 0;
    let mut v_unused_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut v_a_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5168_: u8 = 0;
    let mut v_leanOpts_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5171_: u8 = 0;
    let mut v_printPrefix_5172_: u8 = 0;
    let mut v_printLibDir_5173_: u8 = 0;
    let mut v_useStdin_5174_: u8 = 0;
    let mut v_onlyDeps_5175_: u8 = 0;
    let mut v_onlySrcDeps_5176_: u8 = 0;
    let mut v_depsJson_5177_: u8 = 0;
    let mut v_opts_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5179_: u32 = 0;
    let mut v_numThreads_5180_: u32 = 0;
    let mut v_rootDir_x3f_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5186_: u8 = 0;
    let mut v_errorOnKinds_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5188_: u8 = 0;
    let mut v_run_5189_: u8 = 0;
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5192_: u8 = 0;
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5200_: u8 = 0;
    let mut v_unused_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut v_a_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5214_: u8 = 0;
    let mut v_leanOpts_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5217_: u8 = 0;
    let mut v_printPrefix_5218_: u8 = 0;
    let mut v_printLibDir_5219_: u8 = 0;
    let mut v_useStdin_5220_: u8 = 0;
    let mut v_onlyDeps_5221_: u8 = 0;
    let mut v_onlySrcDeps_5222_: u8 = 0;
    let mut v_depsJson_5223_: u8 = 0;
    let mut v_opts_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5225_: u32 = 0;
    let mut v_numThreads_5226_: u32 = 0;
    let mut v_rootDir_x3f_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5232_: u8 = 0;
    let mut v_errorOnKinds_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5234_: u8 = 0;
    let mut v_run_5235_: u8 = 0;
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut v_unused_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5248_: u8 = 0;
    let mut v_a_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5257_: u8 = 0;
    let mut v_printPrefix_5258_: u8 = 0;
    let mut v_printLibDir_5259_: u8 = 0;
    let mut v_useStdin_5260_: u8 = 0;
    let mut v_onlyDeps_5261_: u8 = 0;
    let mut v_onlySrcDeps_5262_: u8 = 0;
    let mut v_depsJson_5263_: u8 = 0;
    let mut v_opts_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5265_: u32 = 0;
    let mut v_numThreads_5266_: u32 = 0;
    let mut v_rootDir_x3f_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5273_: u8 = 0;
    let mut v_errorOnKinds_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5275_: u8 = 0;
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5278_: u8 = 0;
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5285_: u8 = 0;
    let mut v_leanOpts_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5288_: u8 = 0;
    let mut v_printPrefix_5289_: u8 = 0;
    let mut v_printLibDir_5290_: u8 = 0;
    let mut v_onlyDeps_5291_: u8 = 0;
    let mut v_onlySrcDeps_5292_: u8 = 0;
    let mut v_depsJson_5293_: u8 = 0;
    let mut v_opts_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5295_: u32 = 0;
    let mut v_numThreads_5296_: u32 = 0;
    let mut v_rootDir_x3f_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5303_: u8 = 0;
    let mut v_errorOnKinds_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5305_: u8 = 0;
    let mut v_run_5306_: u8 = 0;
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5309_: u8 = 0;
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5314_: u8 = 0;
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: usize = 0;
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5340_: u8 = 0;
    let mut v_printPrefix_5341_: u8 = 0;
    let mut v_printLibDir_5342_: u8 = 0;
    let mut v_useStdin_5343_: u8 = 0;
    let mut v_onlyDeps_5344_: u8 = 0;
    let mut v_onlySrcDeps_5345_: u8 = 0;
    let mut v_depsJson_5346_: u8 = 0;
    let mut v_opts_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5348_: u32 = 0;
    let mut v_numThreads_5349_: u32 = 0;
    let mut v_rootDir_x3f_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5356_: u8 = 0;
    let mut v_errorOnKinds_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5358_: u8 = 0;
    let mut v_run_5359_: u8 = 0;
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5362_: u8 = 0;
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5372_: u8 = 0;
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v_leanOpts_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5390_: u8 = 0;
    let mut v_printPrefix_5391_: u8 = 0;
    let mut v_printLibDir_5392_: u8 = 0;
    let mut v_useStdin_5393_: u8 = 0;
    let mut v_onlyDeps_5394_: u8 = 0;
    let mut v_onlySrcDeps_5395_: u8 = 0;
    let mut v_depsJson_5396_: u8 = 0;
    let mut v_opts_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5398_: u32 = 0;
    let mut v_numThreads_5399_: u32 = 0;
    let mut v_rootDir_x3f_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5405_: u8 = 0;
    let mut v_errorOnKinds_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5407_: u8 = 0;
    let mut v_run_5408_: u8 = 0;
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5419_: u8 = 0;
    let mut v_unused_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5421_: u8 = 0;
    let mut v_a_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v_leanOpts_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5436_: u8 = 0;
    let mut v_printPrefix_5437_: u8 = 0;
    let mut v_printLibDir_5438_: u8 = 0;
    let mut v_useStdin_5439_: u8 = 0;
    let mut v_onlyDeps_5440_: u8 = 0;
    let mut v_onlySrcDeps_5441_: u8 = 0;
    let mut v_depsJson_5442_: u8 = 0;
    let mut v_opts_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5444_: u32 = 0;
    let mut v_numThreads_5445_: u32 = 0;
    let mut v_rootDir_x3f_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5451_: u8 = 0;
    let mut v_errorOnKinds_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5453_: u8 = 0;
    let mut v_run_5454_: u8 = 0;
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5457_: u8 = 0;
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5465_: u8 = 0;
    let mut v_unused_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v_a_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5478_: u8 = 0;
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5483_: u8 = 0;
    let mut v_unused_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5494_: u8 = 0;
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5499_: u8 = 0;
    let mut v_unused_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5511_: u8 = 0;
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5516_: u8 = 0;
    let mut v_unused_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5533_: u8 = 0;
    let mut v_unused_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5545_: u8 = 0;
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5550_: u8 = 0;
    let mut v_unused_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5563_: u8 = 0;
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: u8 = 0;
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5575_: u8 = 0;
    let mut v_printPrefix_5576_: u8 = 0;
    let mut v_printLibDir_5577_: u8 = 0;
    let mut v_useStdin_5578_: u8 = 0;
    let mut v_onlyDeps_5579_: u8 = 0;
    let mut v_onlySrcDeps_5580_: u8 = 0;
    let mut v_depsJson_5581_: u8 = 0;
    let mut v_opts_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_5583_: u32 = 0;
    let mut v_rootDir_x3f_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5590_: u8 = 0;
    let mut v_errorOnKinds_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5592_: u8 = 0;
    let mut v_run_5593_: u8 = 0;
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5596_: u8 = 0;
    let mut v___x_5597_: u32 = 0;
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5607_: u8 = 0;
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5610_: u8 = 0;
    let mut v_a_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4328_ = 101;
                v___x_4329_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4328_);
                if v___x_4329_ == 0 {
                    v___x_4330_ = 106;
                    v___x_4331_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4330_);
                    if v___x_4331_ == 0 {
                        v___x_4332_ = 118;
                        v___x_4333_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4332_);
                        if v___x_4333_ == 0 {
                            v___x_4334_ = 86;
                            v___x_4335_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4334_);
                            if v___x_4335_ == 0 {
                                v___x_4336_ = 103;
                                v___x_4337_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4336_);
                                if v___x_4337_ == 0 {
                                    v___x_4338_ = 104;
                                    v___x_4339_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4338_);
                                    if v___x_4339_ == 0 {
                                        v___x_4340_ = 102;
                                        v___x_4341_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4340_);
                                        if v___x_4341_ == 0 {
                                            v___x_4342_ = 99;
                                            v___x_4343_ =
                                                lean_uint32_dec_eq(v_opt_4129_, v___x_4342_);
                                            if v___x_4343_ == 0 {
                                                v___x_4344_ = 98;
                                                v___x_4345_ =
                                                    lean_uint32_dec_eq(v_opt_4129_, v___x_4344_);
                                                if v___x_4345_ == 0 {
                                                    v___x_4346_ = 115;
                                                    v___x_4347_ = lean_uint32_dec_eq(
                                                        v_opt_4129_,
                                                        v___x_4346_,
                                                    );
                                                    if v___x_4347_ == 0 {
                                                        v___x_4348_ = 73;
                                                        v___x_4349_ = lean_uint32_dec_eq(
                                                            v_opt_4129_,
                                                            v___x_4348_,
                                                        );
                                                        if v___x_4349_ == 0 {
                                                            v___x_4350_ = 114;
                                                            v___x_4351_ = lean_uint32_dec_eq(
                                                                v_opt_4129_,
                                                                v___x_4350_,
                                                            );
                                                            if v___x_4351_ == 0 {
                                                                v___x_4352_ = 111;
                                                                v___x_4353_ = lean_uint32_dec_eq(
                                                                    v_opt_4129_,
                                                                    v___x_4352_,
                                                                );
                                                                if v___x_4353_ == 0 {
                                                                    v___x_4354_ = 105;
                                                                    v___x_4355_ =
                                                                        lean_uint32_dec_eq(
                                                                            v_opt_4129_,
                                                                            v___x_4354_,
                                                                        );
                                                                    if v___x_4355_ == 0 {
                                                                        v___x_4356_ = 82;
                                                                        v___x_4357_ =
                                                                            lean_uint32_dec_eq(
                                                                                v_opt_4129_,
                                                                                v___x_4356_,
                                                                            );
                                                                        if v___x_4357_ == 0 {
                                                                            v___x_4358_ = 77;
                                                                            v___x_4359_ =
                                                                                lean_uint32_dec_eq(
                                                                                    v_opt_4129_,
                                                                                    v___x_4358_,
                                                                                );
                                                                            if v___x_4359_ == 0 {
                                                                                v___x_4360_ = 84;
                                                                                v___x_4361_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4360_);
                                                                                if v___x_4361_ == 0
                                                                                {
                                                                                    v___x_4362_ =
                                                                                        116;
                                                                                    v___x_4363_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4362_);
                                                                                    if v___x_4363_
                                                                                        == 0
                                                                                    {
                                                                                        v___x_4364_ = 113;
                                                                                        v___x_4365_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4364_);
                                                                                        if v___x_4365_ == 0 {
v___x_4366_ = 100;
v___x_4367_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4366_);
if v___x_4367_ == 0 {
v___x_4368_ = 79;
v___x_4369_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4368_);
if v___x_4369_ == 0 {
v___x_4370_ = 78;
v___x_4371_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4370_);
if v___x_4371_ == 0 {
v___x_4372_ = 74;
v___x_4373_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4372_);
if v___x_4373_ == 0 {
v___x_4374_ = 97;
v___x_4375_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4374_);
if v___x_4375_ == 0 {
v___x_4376_ = 120;
v___x_4377_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4376_);
if v___x_4377_ == 0 {
v___x_4378_ = 76;
v___x_4379_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4378_);
if v___x_4379_ == 0 {
v___x_4380_ = 68;
v___x_4381_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4380_);
if v___x_4381_ == 0 {
v___x_4382_ = 83;
v___x_4383_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4382_);
if v___x_4383_ == 0 {
v___x_4384_ = 87;
v___x_4385_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4384_);
if v___x_4385_ == 0 {
v___x_4386_ = 80;
v___x_4387_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4386_);
if v___x_4387_ == 0 {
v___x_4388_ = 66;
v___x_4389_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4388_);
if v___x_4389_ == 0 {
v___x_4390_ = 112;
v___x_4391_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4390_);
if v___x_4391_ == 0 {
v___x_4392_ = 108;
v___x_4393_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4392_);
if v___x_4393_ == 0 {
v___x_4394_ = 117;
v___x_4395_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4394_);
if v___x_4395_ == 0 {
v___x_4396_ = 69;
v___x_4397_ = lean_uint32_dec_eq(v_opt_4129_, v___x_4396_);
if v___x_4397_ == 0 {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
crate::leanh::lean_dec_ref(v_opts_4128_);
state = 38; continue;
} else {
v___x_4398_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1;
v___x_4399_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_4398_, v_optArg_x3f_4130_);
if crate::leanh::lean_obj_tag(v___x_4399_) == 0 {
v_a_4400_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4438_ = (!crate::leanh::lean_is_exclusive(v___x_4399_)) as u8;
if v_isSharedCheck_4438_ == 0 {
v___x_4402_ = v___x_4399_;
v_isShared_4403_ = v_isSharedCheck_4438_;
state = 64; continue;
} else {
crate::leanh::lean_inc(v_a_4400_);
crate::leanh::lean_dec(v___x_4399_);
v___x_4402_ = crate::leanh::lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4438_;
state = 64; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_4439_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
crate::leanh::lean_inc(v_a_4439_);
crate::leanh::lean_dec_ref_known(v___x_4399_, 1);
v___x_4443_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4444_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4443_);
crate::leanh::lean_dec_ref(v___x_4444_);
state = 68; continue;
}
}
} else {
v___x_4445_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2;
v___x_4446_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_4445_, v_optArg_x3f_4130_);
if crate::leanh::lean_obj_tag(v___x_4446_) == 0 {
v_a_4447_ = crate::leanh::lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4484_ = (!crate::leanh::lean_is_exclusive(v___x_4446_)) as u8;
if v_isSharedCheck_4484_ == 0 {
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4484_;
state = 69; continue;
} else {
crate::leanh::lean_inc(v_a_4447_);
crate::leanh::lean_dec(v___x_4446_);
v___x_4449_ = crate::leanh::lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4484_;
state = 69; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_4485_ = crate::leanh::lean_ctor_get(v___x_4446_, 0);
crate::leanh::lean_inc(v_a_4485_);
crate::leanh::lean_dec_ref_known(v___x_4446_, 1);
v___x_4489_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4490_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4489_);
crate::leanh::lean_dec_ref(v___x_4490_);
state = 73; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v___x_4491_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3;
v___x_4492_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_4491_, v_optArg_x3f_4130_);
if crate::leanh::lean_obj_tag(v___x_4492_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_4492_, 1);
v___x_4493_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4;
v___x_4494_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v___x_4493_);
if crate::leanh::lean_obj_tag(v___x_4494_) == 0 {
v_isSharedCheck_4502_ = (!crate::leanh::lean_is_exclusive(v___x_4494_)) as u8;
if v_isSharedCheck_4502_ == 0 {
v_unused_4503_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
crate::leanh::lean_dec(v_unused_4503_);
v___x_4496_ = v___x_4494_;
v_isShared_4497_ = v_isSharedCheck_4502_;
state = 74; continue;
} else {
crate::leanh::lean_dec(v___x_4494_);
v___x_4496_ = crate::leanh::lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4502_;
state = 74; continue;
}
} else {
v_a_4504_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
crate::leanh::lean_inc(v_a_4504_);
crate::leanh::lean_dec_ref_known(v___x_4494_, 1);
v___x_4508_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4509_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4508_);
crate::leanh::lean_dec_ref(v___x_4509_);
state = 76; continue;
}
} else {
v_a_4510_ = crate::leanh::lean_ctor_get(v___x_4492_, 0);
crate::leanh::lean_inc(v_a_4510_);
crate::leanh::lean_dec_ref_known(v___x_4492_, 1);
v___x_4514_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4515_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4514_);
crate::leanh::lean_dec_ref(v___x_4515_);
state = 77; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v___x_4516_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5;
v___x_4517_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_4516_, v_optArg_x3f_4130_);
if crate::leanh::lean_obj_tag(v___x_4517_) == 0 {
crate::leanh::lean_dec_ref_known(v___x_4517_, 1);
v___x_4518_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6;
v___x_4519_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v___x_4518_);
if crate::leanh::lean_obj_tag(v___x_4519_) == 0 {
v_isSharedCheck_4527_ = (!crate::leanh::lean_is_exclusive(v___x_4519_)) as u8;
if v_isSharedCheck_4527_ == 0 {
v_unused_4528_ = crate::leanh::lean_ctor_get(v___x_4519_, 0);
crate::leanh::lean_dec(v_unused_4528_);
v___x_4521_ = v___x_4519_;
v_isShared_4522_ = v_isSharedCheck_4527_;
state = 78; continue;
} else {
crate::leanh::lean_dec(v___x_4519_);
v___x_4521_ = crate::leanh::lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4527_;
state = 78; continue;
}
} else {
v_a_4529_ = crate::leanh::lean_ctor_get(v___x_4519_, 0);
crate::leanh::lean_inc(v_a_4529_);
crate::leanh::lean_dec_ref_known(v___x_4519_, 1);
v___x_4533_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4534_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4533_);
crate::leanh::lean_dec_ref(v___x_4534_);
state = 80; continue;
}
} else {
v_a_4535_ = crate::leanh::lean_ctor_get(v___x_4517_, 0);
crate::leanh::lean_inc(v_a_4535_);
crate::leanh::lean_dec_ref_known(v___x_4517_, 1);
v___x_4539_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4540_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4539_);
crate::leanh::lean_dec_ref(v___x_4540_);
state = 81; continue;
}
}
} else {
v___x_4541_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once), _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if v___x_4541_ == 0 {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
crate::leanh::lean_dec_ref(v_opts_4128_);
state = 38; continue;
} else {
v___x_4542_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7;
v___x_4543_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_4542_, v_optArg_x3f_4130_);
if crate::leanh::lean_obj_tag(v___x_4543_) == 0 {
v_a_4544_ = crate::leanh::lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4552_ = (!crate::leanh::lean_is_exclusive(v___x_4543_)) as u8;
if v_isSharedCheck_4552_ == 0 {
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4552_;
state = 82; continue;
} else {
crate::leanh::lean_inc(v_a_4544_);
crate::leanh::lean_dec(v___x_4543_);
v___x_4546_ = crate::leanh::lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4552_;
state = 82; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_4553_ = crate::leanh::lean_ctor_get(v___x_4543_, 0);
crate::leanh::lean_inc(v_a_4553_);
crate::leanh::lean_dec_ref_known(v___x_4543_, 1);
v___x_4557_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4558_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4557_);
crate::leanh::lean_dec_ref(v___x_4558_);
state = 84; continue;
}
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4559_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4560_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4561_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4562_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4563_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4564_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4565_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4566_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4567_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4568_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4569_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4570_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4571_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4572_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4573_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4574_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4575_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4576_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4577_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4578_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4579_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4580_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4590_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4590_ == 0 {
v___x_4582_ = v_opts_4128_;
v_isShared_4583_ = v_isSharedCheck_4590_;
state = 85; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4578_);
crate::leanh::lean_inc(v_bcFileName_x3f_4576_);
crate::leanh::lean_inc(v_rustFileName_x3f_4575_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4574_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4573_);
crate::leanh::lean_inc(v_setupFileName_x3f_4572_);
crate::leanh::lean_inc(v_rootDir_x3f_4571_);
crate::leanh::lean_inc(v_opts_4568_);
crate::leanh::lean_inc(v_forwardedArgs_4560_);
crate::leanh::lean_inc(v_leanOpts_4559_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4582_ = crate::leanh::lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4590_;
state = 85; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4591_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4592_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_printPrefix_4593_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4594_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4595_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4596_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4597_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4598_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4599_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4600_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4601_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4602_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4603_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4604_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4605_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4606_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4607_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4608_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4609_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4610_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4611_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4620_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4620_ == 0 {
v___x_4613_ = v_opts_4128_;
v_isShared_4614_ = v_isSharedCheck_4620_;
state = 87; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4609_);
crate::leanh::lean_inc(v_bcFileName_x3f_4607_);
crate::leanh::lean_inc(v_rustFileName_x3f_4606_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4605_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4604_);
crate::leanh::lean_inc(v_setupFileName_x3f_4603_);
crate::leanh::lean_inc(v_rootDir_x3f_4602_);
crate::leanh::lean_inc(v_opts_4599_);
crate::leanh::lean_inc(v_forwardedArgs_4592_);
crate::leanh::lean_inc(v_leanOpts_4591_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4613_ = crate::leanh::lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4620_;
state = 87; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4621_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4622_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_printPrefix_4623_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4624_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4625_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4626_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4627_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4628_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4629_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4630_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4631_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4632_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4633_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4634_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4635_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4636_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4637_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4638_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4639_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4640_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4641_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4650_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4650_ == 0 {
v___x_4643_ = v_opts_4128_;
v_isShared_4644_ = v_isSharedCheck_4650_;
state = 89; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4639_);
crate::leanh::lean_inc(v_bcFileName_x3f_4637_);
crate::leanh::lean_inc(v_rustFileName_x3f_4636_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4635_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4634_);
crate::leanh::lean_inc(v_setupFileName_x3f_4633_);
crate::leanh::lean_inc(v_rootDir_x3f_4632_);
crate::leanh::lean_inc(v_opts_4629_);
crate::leanh::lean_inc(v_forwardedArgs_4622_);
crate::leanh::lean_inc(v_leanOpts_4621_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4643_ = crate::leanh::lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4650_;
state = 89; continue;
}
}
} else {
v___x_4651_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8;
v___x_4652_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_4651_, v_optArg_x3f_4130_);
if crate::leanh::lean_obj_tag(v___x_4652_) == 0 {
v_a_4653_ = crate::leanh::lean_ctor_get(v___x_4652_, 0);
crate::leanh::lean_inc(v_a_4653_);
crate::leanh::lean_dec_ref_known(v___x_4652_, 1);
v_leanOpts_4654_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4655_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4656_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4657_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4658_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4659_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4660_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4661_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4662_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4663_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4664_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4665_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4666_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4667_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4668_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4669_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4670_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4671_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4672_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4673_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4674_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4675_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4700_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4700_ == 0 {
v___x_4677_ = v_opts_4128_;
v_isShared_4678_ = v_isSharedCheck_4700_;
state = 91; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4673_);
crate::leanh::lean_inc(v_bcFileName_x3f_4671_);
crate::leanh::lean_inc(v_rustFileName_x3f_4670_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4669_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4668_);
crate::leanh::lean_inc(v_setupFileName_x3f_4667_);
crate::leanh::lean_inc(v_rootDir_x3f_4666_);
crate::leanh::lean_inc(v_opts_4663_);
crate::leanh::lean_inc(v_forwardedArgs_4655_);
crate::leanh::lean_inc(v_leanOpts_4654_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4677_ = crate::leanh::lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4700_;
state = 91; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_4701_ = crate::leanh::lean_ctor_get(v___x_4652_, 0);
crate::leanh::lean_inc(v_a_4701_);
crate::leanh::lean_dec_ref_known(v___x_4652_, 1);
v___x_4705_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4706_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4705_);
crate::leanh::lean_dec_ref(v___x_4706_);
state = 96; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4707_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4708_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4709_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4710_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_useStdin_4711_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4712_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4713_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4714_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4715_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4716_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4717_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4718_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4719_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4720_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4721_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4722_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4723_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4724_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4725_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4726_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4727_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4735_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4735_ == 0 {
v___x_4729_ = v_opts_4128_;
v_isShared_4730_ = v_isSharedCheck_4735_;
state = 97; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4725_);
crate::leanh::lean_inc(v_bcFileName_x3f_4723_);
crate::leanh::lean_inc(v_rustFileName_x3f_4722_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4721_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4720_);
crate::leanh::lean_inc(v_setupFileName_x3f_4719_);
crate::leanh::lean_inc(v_rootDir_x3f_4718_);
crate::leanh::lean_inc(v_opts_4715_);
crate::leanh::lean_inc(v_forwardedArgs_4708_);
crate::leanh::lean_inc(v_leanOpts_4707_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4729_ = crate::leanh::lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4735_;
state = 97; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4736_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4737_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4738_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printLibDir_4739_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4740_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4741_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4742_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4743_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4744_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4745_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4746_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4747_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4748_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4749_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4750_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4751_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4752_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4753_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4754_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4755_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4756_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4764_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4764_ == 0 {
v___x_4758_ = v_opts_4128_;
v_isShared_4759_ = v_isSharedCheck_4764_;
state = 99; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4754_);
crate::leanh::lean_inc(v_bcFileName_x3f_4752_);
crate::leanh::lean_inc(v_rustFileName_x3f_4751_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4750_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4749_);
crate::leanh::lean_inc(v_setupFileName_x3f_4748_);
crate::leanh::lean_inc(v_rootDir_x3f_4747_);
crate::leanh::lean_inc(v_opts_4744_);
crate::leanh::lean_inc(v_forwardedArgs_4737_);
crate::leanh::lean_inc(v_leanOpts_4736_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4758_ = crate::leanh::lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4764_;
state = 99; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4765_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4766_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4767_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4768_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4769_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4770_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4771_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4772_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4773_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4774_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4775_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4776_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4777_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4778_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4779_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4780_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4781_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4782_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4783_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4784_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_run_4785_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4793_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4793_ == 0 {
v___x_4787_ = v_opts_4128_;
v_isShared_4788_ = v_isSharedCheck_4793_;
state = 101; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4784_);
crate::leanh::lean_inc(v_bcFileName_x3f_4782_);
crate::leanh::lean_inc(v_rustFileName_x3f_4781_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4780_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4779_);
crate::leanh::lean_inc(v_setupFileName_x3f_4778_);
crate::leanh::lean_inc(v_rootDir_x3f_4777_);
crate::leanh::lean_inc(v_opts_4774_);
crate::leanh::lean_inc(v_forwardedArgs_4766_);
crate::leanh::lean_inc(v_leanOpts_4765_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4787_ = crate::leanh::lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4793_;
state = 101; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4794_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4795_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4796_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4797_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4798_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4799_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4800_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4801_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4802_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4803_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4804_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4805_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4806_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4807_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4808_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4809_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4810_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4811_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_errorOnKinds_4812_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4813_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4814_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4822_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4822_ == 0 {
v___x_4816_ = v_opts_4128_;
v_isShared_4817_ = v_isSharedCheck_4822_;
state = 103; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4812_);
crate::leanh::lean_inc(v_bcFileName_x3f_4811_);
crate::leanh::lean_inc(v_rustFileName_x3f_4810_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4809_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4808_);
crate::leanh::lean_inc(v_setupFileName_x3f_4807_);
crate::leanh::lean_inc(v_rootDir_x3f_4806_);
crate::leanh::lean_inc(v_opts_4803_);
crate::leanh::lean_inc(v_forwardedArgs_4795_);
crate::leanh::lean_inc(v_leanOpts_4794_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4816_ = crate::leanh::lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4822_;
state = 103; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4823_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4824_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4825_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4826_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4827_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4828_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlySrcDeps_4829_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_opts_4830_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4831_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4832_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4833_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4834_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4835_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4836_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4837_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4838_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4839_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4840_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4841_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4842_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4850_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4850_ == 0 {
v___x_4844_ = v_opts_4128_;
v_isShared_4845_ = v_isSharedCheck_4850_;
state = 105; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4840_);
crate::leanh::lean_inc(v_bcFileName_x3f_4838_);
crate::leanh::lean_inc(v_rustFileName_x3f_4837_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4836_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4835_);
crate::leanh::lean_inc(v_setupFileName_x3f_4834_);
crate::leanh::lean_inc(v_rootDir_x3f_4833_);
crate::leanh::lean_inc(v_opts_4830_);
crate::leanh::lean_inc(v_forwardedArgs_4824_);
crate::leanh::lean_inc(v_leanOpts_4823_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4844_ = crate::leanh::lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4850_;
state = 105; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4851_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4852_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4853_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4854_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4855_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4856_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4857_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_depsJson_4858_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4859_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4860_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4861_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4862_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4863_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4864_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4865_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4866_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4867_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4868_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4869_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4870_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4871_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4879_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4879_ == 0 {
v___x_4873_ = v_opts_4128_;
v_isShared_4874_ = v_isSharedCheck_4879_;
state = 107; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4869_);
crate::leanh::lean_inc(v_bcFileName_x3f_4867_);
crate::leanh::lean_inc(v_rustFileName_x3f_4866_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4865_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4864_);
crate::leanh::lean_inc(v_setupFileName_x3f_4863_);
crate::leanh::lean_inc(v_rootDir_x3f_4862_);
crate::leanh::lean_inc(v_opts_4859_);
crate::leanh::lean_inc(v_forwardedArgs_4852_);
crate::leanh::lean_inc(v_leanOpts_4851_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4873_ = crate::leanh::lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4879_;
state = 107; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4880_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4881_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4882_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4883_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4884_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4885_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlySrcDeps_4886_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4887_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4888_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4889_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4890_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4891_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4892_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4893_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4894_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4895_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4896_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4897_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4898_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4899_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4900_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4908_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4908_ == 0 {
v___x_4902_ = v_opts_4128_;
v_isShared_4903_ = v_isSharedCheck_4908_;
state = 109; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4898_);
crate::leanh::lean_inc(v_bcFileName_x3f_4896_);
crate::leanh::lean_inc(v_rustFileName_x3f_4895_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4894_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4893_);
crate::leanh::lean_inc(v_setupFileName_x3f_4892_);
crate::leanh::lean_inc(v_rootDir_x3f_4891_);
crate::leanh::lean_inc(v_opts_4888_);
crate::leanh::lean_inc(v_forwardedArgs_4881_);
crate::leanh::lean_inc(v_leanOpts_4880_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4902_ = crate::leanh::lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4908_;
state = 109; continue;
}
}
} else {
crate::leanh::lean_dec(v_optArg_x3f_4130_);
v_leanOpts_4909_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
v_forwardedArgs_4910_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
v_component_4911_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
v_printPrefix_4912_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
v_printLibDir_4913_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
v_useStdin_4914_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
v_onlyDeps_4915_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
v_onlySrcDeps_4916_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
v_depsJson_4917_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
v_opts_4918_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
v_trustLevel_4919_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
v_numThreads_4920_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
v_rootDir_x3f_4921_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
v_setupFileName_x3f_4922_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
v_oleanFileName_x3f_4923_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
v_ileanFileName_x3f_4924_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
v_rustFileName_x3f_4925_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
v_bcFileName_x3f_4926_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
v_jsonOutput_4927_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
v_errorOnKinds_4928_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
v_printStats_4929_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
v_run_4930_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
v_isSharedCheck_4940_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
if v_isSharedCheck_4940_ == 0 {
v___x_4932_ = v_opts_4128_;
v_isShared_4933_ = v_isSharedCheck_4940_;
state = 111; continue;
} else {
crate::leanh::lean_inc(v_errorOnKinds_4928_);
crate::leanh::lean_inc(v_bcFileName_x3f_4926_);
crate::leanh::lean_inc(v_rustFileName_x3f_4925_);
crate::leanh::lean_inc(v_ileanFileName_x3f_4924_);
crate::leanh::lean_inc(v_oleanFileName_x3f_4923_);
crate::leanh::lean_inc(v_setupFileName_x3f_4922_);
crate::leanh::lean_inc(v_rootDir_x3f_4921_);
crate::leanh::lean_inc(v_opts_4918_);
crate::leanh::lean_inc(v_forwardedArgs_4910_);
crate::leanh::lean_inc(v_leanOpts_4909_);
crate::leanh::lean_dec(v_opts_4128_);
v___x_4932_ = crate::leanh::lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4940_;
state = 111; continue;
}
}
                                                                                    } else {
                                                                                        v___x_4941_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10;
                                                                                        v___x_4942_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_4941_, v_optArg_x3f_4130_);
                                                                                        if crate::leanh::lean_obj_tag(v___x_4942_) == 0 {
v_a_4943_ = crate::leanh::lean_ctor_get(v___x_4942_, 0);
v_isSharedCheck_4993_ = (!crate::leanh::lean_is_exclusive(v___x_4942_)) as u8;
if v_isSharedCheck_4993_ == 0 {
v___x_4945_ = v___x_4942_;
v_isShared_4946_ = v_isSharedCheck_4993_;
state = 113; continue;
} else {
crate::leanh::lean_inc(v_a_4943_);
crate::leanh::lean_dec(v___x_4942_);
v___x_4945_ = crate::leanh::lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4993_;
state = 113; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_4994_ = crate::leanh::lean_ctor_get(v___x_4942_, 0);
crate::leanh::lean_inc(v_a_4994_);
crate::leanh::lean_dec_ref_known(v___x_4942_, 1);
v___x_4998_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_4999_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4998_);
crate::leanh::lean_dec_ref(v___x_4999_);
state = 117; continue;
}
                                                                                    }
                                                                                } else {
                                                                                    v___x_5000_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14;
                                                                                    v___x_5001_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_5000_, v_optArg_x3f_4130_);
                                                                                    if crate::leanh::lean_obj_tag(v___x_5001_) == 0 {
v_a_5002_ = crate::leanh::lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5050_ = (!crate::leanh::lean_is_exclusive(v___x_5001_)) as u8;
if v_isSharedCheck_5050_ == 0 {
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5050_;
state = 118; continue;
} else {
crate::leanh::lean_inc(v_a_5002_);
crate::leanh::lean_dec(v___x_5001_);
v___x_5004_ = crate::leanh::lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5050_;
state = 118; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_5051_ = crate::leanh::lean_ctor_get(v___x_5001_, 0);
crate::leanh::lean_inc(v_a_5051_);
crate::leanh::lean_dec_ref_known(v___x_5001_, 1);
v___x_5055_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_5056_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5055_);
crate::leanh::lean_dec_ref(v___x_5056_);
state = 122; continue;
}
                                                                                }
                                                                            } else {
                                                                                v___x_5057_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17;
                                                                                v___x_5058_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_5057_, v_optArg_x3f_4130_);
                                                                                if crate::leanh::lean_obj_tag(v___x_5058_) == 0 {
v_a_5059_ = crate::leanh::lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5107_ = (!crate::leanh::lean_is_exclusive(v___x_5058_)) as u8;
if v_isSharedCheck_5107_ == 0 {
v___x_5061_ = v___x_5058_;
v_isShared_5062_ = v_isSharedCheck_5107_;
state = 123; continue;
} else {
crate::leanh::lean_inc(v_a_5059_);
crate::leanh::lean_dec(v___x_5058_);
v___x_5061_ = crate::leanh::lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5107_;
state = 123; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_5108_ = crate::leanh::lean_ctor_get(v___x_5058_, 0);
crate::leanh::lean_inc(v_a_5108_);
crate::leanh::lean_dec_ref_known(v___x_5058_, 1);
v___x_5112_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_5113_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5112_);
crate::leanh::lean_dec_ref(v___x_5113_);
state = 127; continue;
}
                                                                            }
                                                                        } else {
                                                                            v___x_5114_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20;
                                                                            v___x_5115_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_5114_, v_optArg_x3f_4130_);
                                                                            if crate::leanh::lean_obj_tag(v___x_5115_) == 0 {
v_a_5116_ = crate::leanh::lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5156_ = (!crate::leanh::lean_is_exclusive(v___x_5115_)) as u8;
if v_isSharedCheck_5156_ == 0 {
v___x_5118_ = v___x_5115_;
v_isShared_5119_ = v_isSharedCheck_5156_;
state = 128; continue;
} else {
crate::leanh::lean_inc(v_a_5116_);
crate::leanh::lean_dec(v___x_5115_);
v___x_5118_ = crate::leanh::lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5156_;
state = 128; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_5157_ = crate::leanh::lean_ctor_get(v___x_5115_, 0);
crate::leanh::lean_inc(v_a_5157_);
crate::leanh::lean_dec_ref_known(v___x_5115_, 1);
v___x_5161_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_5162_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5161_);
crate::leanh::lean_dec_ref(v___x_5162_);
state = 132; continue;
}
                                                                        }
                                                                    } else {
                                                                        v___x_5163_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22;
                                                                        v___x_5164_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_5163_, v_optArg_x3f_4130_);
                                                                        if crate::leanh::lean_obj_tag(v___x_5164_) == 0 {
v_a_5165_ = crate::leanh::lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5202_ = (!crate::leanh::lean_is_exclusive(v___x_5164_)) as u8;
if v_isSharedCheck_5202_ == 0 {
v___x_5167_ = v___x_5164_;
v_isShared_5168_ = v_isSharedCheck_5202_;
state = 133; continue;
} else {
crate::leanh::lean_inc(v_a_5165_);
crate::leanh::lean_dec(v___x_5164_);
v___x_5167_ = crate::leanh::lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5202_;
state = 133; continue;
}
} else {
crate::leanh::lean_dec_ref(v_opts_4128_);
v_a_5203_ = crate::leanh::lean_ctor_get(v___x_5164_, 0);
crate::leanh::lean_inc(v_a_5203_);
crate::leanh::lean_dec_ref_known(v___x_5164_, 1);
v___x_5207_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
v___x_5208_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5207_);
crate::leanh::lean_dec_ref(v___x_5208_);
state = 137; continue;
}
                                                                    }
                                                                } else {
                                                                    v___x_5209_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23;
                                                                    v___x_5210_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_5209_, v_optArg_x3f_4130_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_5210_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_5211_ = crate::leanh::lean_ctor_get(v___x_5210_, 0);
                                                                        v_isSharedCheck_5248_ = (!crate::leanh::lean_is_exclusive(v___x_5210_)) as u8;
                                                                        if v_isSharedCheck_5248_
                                                                            == 0
                                                                        {
                                                                            v___x_5213_ =
                                                                                v___x_5210_;
                                                                            v_isShared_5214_ = v_isSharedCheck_5248_;
                                                                            state = 138;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_5211_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_5210_,
                                                                            );
                                                                            v___x_5213_ = crate::leanh::lean_box(0);
                                                                            v_isShared_5214_ = v_isSharedCheck_5248_;
                                                                            state = 138;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_opts_4128_,
                                                                        );
                                                                        v_a_5249_ = crate::leanh::lean_ctor_get(v___x_5210_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_5249_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_5210_, 1);
                                                                        v___x_5253_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                                                        v___x_5254_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5253_);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_5254_,
                                                                        );
                                                                        state = 142;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(
                                                                    v_optArg_x3f_4130_,
                                                                );
                                                                v_leanOpts_5255_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        0,
                                                                    );
                                                                v_forwardedArgs_5256_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        1,
                                                                    );
                                                                v_component_5257_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
                                                                v_printPrefix_5258_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
                                                                v_printLibDir_5259_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
                                                                v_useStdin_5260_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 11) as u32);
                                                                v_onlyDeps_5261_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
                                                                v_onlySrcDeps_5262_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
                                                                v_depsJson_5263_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
                                                                v_opts_5264_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        2,
                                                                    );
                                                                v_trustLevel_5265_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
                                                                v_numThreads_5266_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
                                                                v_rootDir_x3f_5267_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        3,
                                                                    );
                                                                v_setupFileName_x3f_5268_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        4,
                                                                    );
                                                                v_oleanFileName_x3f_5269_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        5,
                                                                    );
                                                                v_ileanFileName_x3f_5270_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        6,
                                                                    );
                                                                v_rustFileName_x3f_5271_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        7,
                                                                    );
                                                                v_bcFileName_x3f_5272_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        8,
                                                                    );
                                                                v_jsonOutput_5273_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
                                                                v_errorOnKinds_5274_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_opts_4128_,
                                                                        9,
                                                                    );
                                                                v_printStats_5275_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
                                                                v_isSharedCheck_5285_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                                                                if v_isSharedCheck_5285_ == 0 {
                                                                    v___x_5277_ = v_opts_4128_;
                                                                    v_isShared_5278_ =
                                                                        v_isSharedCheck_5285_;
                                                                    state = 143;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_errorOnKinds_5274_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_bcFileName_x3f_5272_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_rustFileName_x3f_5271_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_ileanFileName_x3f_5270_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_oleanFileName_x3f_5269_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_setupFileName_x3f_5268_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_rootDir_x3f_5267_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_opts_5264_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_forwardedArgs_5256_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_leanOpts_5255_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_opts_4128_,
                                                                    );
                                                                    v___x_5277_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_5278_ =
                                                                        v_isSharedCheck_5285_;
                                                                    state = 143;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(
                                                                v_optArg_x3f_4130_,
                                                            );
                                                            v_leanOpts_5286_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    0,
                                                                );
                                                            v_forwardedArgs_5287_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    1,
                                                                );
                                                            v_component_5288_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 8) as u32);
                                                            v_printPrefix_5289_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 9) as u32);
                                                            v_printLibDir_5290_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 10) as u32);
                                                            v_onlyDeps_5291_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 12) as u32);
                                                            v_onlySrcDeps_5292_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 13) as u32);
                                                            v_depsJson_5293_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 14) as u32);
                                                            v_opts_5294_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    2,
                                                                );
                                                            v_trustLevel_5295_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u32);
                                                            v_numThreads_5296_ = crate::leanh::lean_ctor_get_uint32(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 4) as u32);
                                                            v_rootDir_x3f_5297_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    3,
                                                                );
                                                            v_setupFileName_x3f_5298_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    4,
                                                                );
                                                            v_oleanFileName_x3f_5299_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    5,
                                                                );
                                                            v_ileanFileName_x3f_5300_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    6,
                                                                );
                                                            v_rustFileName_x3f_5301_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    7,
                                                                );
                                                            v_bcFileName_x3f_5302_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    8,
                                                                );
                                                            v_jsonOutput_5303_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 15) as u32);
                                                            v_errorOnKinds_5304_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_opts_4128_,
                                                                    9,
                                                                );
                                                            v_printStats_5305_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 16) as u32);
                                                            v_run_5306_ = crate::leanh::lean_ctor_get_uint8(v_opts_4128_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*10 + 17) as u32);
                                                            v_isSharedCheck_5314_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v_opts_4128_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5314_ == 0 {
                                                                v___x_5308_ = v_opts_4128_;
                                                                v_isShared_5309_ =
                                                                    v_isSharedCheck_5314_;
                                                                state = 145;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(
                                                                    v_errorOnKinds_5304_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_bcFileName_x3f_5302_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_rustFileName_x3f_5301_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_ileanFileName_x3f_5300_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_oleanFileName_x3f_5299_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_setupFileName_x3f_5298_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_rootDir_x3f_5297_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_opts_5294_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_forwardedArgs_5287_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_leanOpts_5286_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_opts_4128_,
                                                                );
                                                                v___x_5308_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_5309_ =
                                                                    v_isSharedCheck_5314_;
                                                                state = 145;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        v___x_5315_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24;
                                                        v___x_5316_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_5315_, v_optArg_x3f_4130_);
                                                        if crate::leanh::lean_obj_tag(v___x_5316_)
                                                            == 0
                                                        {
                                                            v_a_5317_ = crate::leanh::lean_ctor_get(
                                                                v___x_5316_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5375_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_5316_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5375_ == 0 {
                                                                v___x_5319_ = v___x_5316_;
                                                                v_isShared_5320_ =
                                                                    v_isSharedCheck_5375_;
                                                                state = 147;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_5317_);
                                                                crate::leanh::lean_dec(v___x_5316_);
                                                                v___x_5319_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_5320_ =
                                                                    v_isSharedCheck_5375_;
                                                                state = 147;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(
                                                                v_opts_4128_,
                                                            );
                                                            v_a_5376_ = crate::leanh::lean_ctor_get(
                                                                v___x_5316_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_5376_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_5316_,
                                                                1,
                                                            );
                                                            v___x_5380_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                                            v___x_5381_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5380_);
                                                            crate::leanh::lean_dec_ref(v___x_5381_);
                                                            state = 151;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    v___x_5382_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29;
                                                    v___x_5383_ =
                                                        l___private_Lean_Shell_0__Lean_checkOptArg(
                                                            v___x_5382_,
                                                            v_optArg_x3f_4130_,
                                                        );
                                                    if crate::leanh::lean_obj_tag(v___x_5383_) == 0
                                                    {
                                                        v_a_5384_ = crate::leanh::lean_ctor_get(
                                                            v___x_5383_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5421_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_5383_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_5421_ == 0 {
                                                            v___x_5386_ = v___x_5383_;
                                                            v_isShared_5387_ =
                                                                v_isSharedCheck_5421_;
                                                            state = 152;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_5384_);
                                                            crate::leanh::lean_dec(v___x_5383_);
                                                            v___x_5386_ = crate::leanh::lean_box(0);
                                                            v_isShared_5387_ =
                                                                v_isSharedCheck_5421_;
                                                            state = 152;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_opts_4128_);
                                                        v_a_5422_ = crate::leanh::lean_ctor_get(
                                                            v___x_5383_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_5422_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_5383_,
                                                            1,
                                                        );
                                                        v___x_5426_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                                        v___x_5427_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5426_);
                                                        crate::leanh::lean_dec_ref(v___x_5427_);
                                                        state = 156;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v___x_5428_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30;
                                                v___x_5429_ =
                                                    l___private_Lean_Shell_0__Lean_checkOptArg(
                                                        v___x_5428_,
                                                        v_optArg_x3f_4130_,
                                                    );
                                                if crate::leanh::lean_obj_tag(v___x_5429_) == 0 {
                                                    v_a_5430_ =
                                                        crate::leanh::lean_ctor_get(v___x_5429_, 0);
                                                    v_isSharedCheck_5467_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5429_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5467_ == 0 {
                                                        v___x_5432_ = v___x_5429_;
                                                        v_isShared_5433_ = v_isSharedCheck_5467_;
                                                        state = 157;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5430_);
                                                        crate::leanh::lean_dec(v___x_5429_);
                                                        v___x_5432_ = crate::leanh::lean_box(0);
                                                        v_isShared_5433_ = v_isSharedCheck_5467_;
                                                        state = 157;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_opts_4128_);
                                                    v_a_5468_ =
                                                        crate::leanh::lean_ctor_get(v___x_5429_, 0);
                                                    crate::leanh::lean_inc(v_a_5468_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_5429_,
                                                        1,
                                                    );
                                                    v___x_5472_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                                    v___x_5473_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5472_);
                                                    crate::leanh::lean_dec_ref(v___x_5473_);
                                                    state = 161;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_optArg_x3f_4130_);
                                            crate::leanh::lean_dec_ref(v_opts_4128_);
                                            v___x_5474_ =
                                                l___private_Lean_Shell_0__Lean_featuresString;
                                            v___x_5475_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_5474_);
                                            if crate::leanh::lean_obj_tag(v___x_5475_) == 0 {
                                                v_isSharedCheck_5483_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5475_))
                                                        as u8;
                                                if v_isSharedCheck_5483_ == 0 {
                                                    v_unused_5484_ =
                                                        crate::leanh::lean_ctor_get(v___x_5475_, 0);
                                                    crate::leanh::lean_dec(v_unused_5484_);
                                                    v___x_5477_ = v___x_5475_;
                                                    v_isShared_5478_ = v_isSharedCheck_5483_;
                                                    state = 162;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_5475_);
                                                    v___x_5477_ = crate::leanh::lean_box(0);
                                                    v_isShared_5478_ = v_isSharedCheck_5483_;
                                                    state = 162;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5485_ =
                                                    crate::leanh::lean_ctor_get(v___x_5475_, 0);
                                                crate::leanh::lean_inc(v_a_5485_);
                                                crate::leanh::lean_dec_ref_known(v___x_5475_, 1);
                                                v___x_5489_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                                v___x_5490_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5489_);
                                                crate::leanh::lean_dec_ref(v___x_5490_);
                                                state = 164;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_optArg_x3f_4130_);
                                        crate::leanh::lean_dec_ref(v_opts_4128_);
                                        v___x_5491_ =
                                            l___private_Lean_Shell_0__Lean_displayHelp(v___x_4337_);
                                        if crate::leanh::lean_obj_tag(v___x_5491_) == 0 {
                                            v_isSharedCheck_5499_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5491_))
                                                    as u8;
                                            if v_isSharedCheck_5499_ == 0 {
                                                v_unused_5500_ =
                                                    crate::leanh::lean_ctor_get(v___x_5491_, 0);
                                                crate::leanh::lean_dec(v_unused_5500_);
                                                v___x_5493_ = v___x_5491_;
                                                v_isShared_5494_ = v_isSharedCheck_5499_;
                                                state = 165;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_5491_);
                                                v___x_5493_ = crate::leanh::lean_box(0);
                                                v_isShared_5494_ = v_isSharedCheck_5499_;
                                                state = 165;
                                                continue;
                                            }
                                        } else {
                                            v_a_5501_ = crate::leanh::lean_ctor_get(v___x_5491_, 0);
                                            crate::leanh::lean_inc(v_a_5501_);
                                            crate::leanh::lean_dec_ref_known(v___x_5491_, 1);
                                            v___x_5505_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                            v___x_5506_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5505_);
                                            crate::leanh::lean_dec_ref(v___x_5506_);
                                            state = 167;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_optArg_x3f_4130_);
                                    crate::leanh::lean_dec_ref(v_opts_4128_);
                                    v___x_5507_ = l_Lean_githash;
                                    v___x_5508_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_5507_);
                                    if crate::leanh::lean_obj_tag(v___x_5508_) == 0 {
                                        v_isSharedCheck_5516_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5508_)) as u8;
                                        if v_isSharedCheck_5516_ == 0 {
                                            v_unused_5517_ =
                                                crate::leanh::lean_ctor_get(v___x_5508_, 0);
                                            crate::leanh::lean_dec(v_unused_5517_);
                                            v___x_5510_ = v___x_5508_;
                                            v_isShared_5511_ = v_isSharedCheck_5516_;
                                            state = 168;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_5508_);
                                            v___x_5510_ = crate::leanh::lean_box(0);
                                            v_isShared_5511_ = v_isSharedCheck_5516_;
                                            state = 168;
                                            continue;
                                        }
                                    } else {
                                        v_a_5518_ = crate::leanh::lean_ctor_get(v___x_5508_, 0);
                                        crate::leanh::lean_inc(v_a_5518_);
                                        crate::leanh::lean_dec_ref_known(v___x_5508_, 1);
                                        v___x_5522_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                        v___x_5523_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5522_);
                                        crate::leanh::lean_dec_ref(v___x_5523_);
                                        state = 170;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_optArg_x3f_4130_);
                                crate::leanh::lean_dec_ref(v_opts_4128_);
                                v___x_5524_ = l___private_Lean_Shell_0__Lean_shortVersionString;
                                v___x_5525_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_5524_);
                                if crate::leanh::lean_obj_tag(v___x_5525_) == 0 {
                                    v_isSharedCheck_5533_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5525_)) as u8;
                                    if v_isSharedCheck_5533_ == 0 {
                                        v_unused_5534_ =
                                            crate::leanh::lean_ctor_get(v___x_5525_, 0);
                                        crate::leanh::lean_dec(v_unused_5534_);
                                        v___x_5527_ = v___x_5525_;
                                        v_isShared_5528_ = v_isSharedCheck_5533_;
                                        state = 171;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_5525_);
                                        v___x_5527_ = crate::leanh::lean_box(0);
                                        v_isShared_5528_ = v_isSharedCheck_5533_;
                                        state = 171;
                                        continue;
                                    }
                                } else {
                                    v_a_5535_ = crate::leanh::lean_ctor_get(v___x_5525_, 0);
                                    crate::leanh::lean_inc(v_a_5535_);
                                    crate::leanh::lean_dec_ref_known(v___x_5525_, 1);
                                    v___x_5539_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                    v___x_5540_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5539_);
                                    crate::leanh::lean_dec_ref(v___x_5540_);
                                    state = 173;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_optArg_x3f_4130_);
                            crate::leanh::lean_dec_ref(v_opts_4128_);
                            v___x_5541_ = l___private_Lean_Shell_0__Lean_versionHeader;
                            v___x_5542_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_5541_);
                            if crate::leanh::lean_obj_tag(v___x_5542_) == 0 {
                                v_isSharedCheck_5550_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5542_)) as u8;
                                if v_isSharedCheck_5550_ == 0 {
                                    v_unused_5551_ = crate::leanh::lean_ctor_get(v___x_5542_, 0);
                                    crate::leanh::lean_dec(v_unused_5551_);
                                    v___x_5544_ = v___x_5542_;
                                    v_isShared_5545_ = v_isSharedCheck_5550_;
                                    state = 174;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_5542_);
                                    v___x_5544_ = crate::leanh::lean_box(0);
                                    v_isShared_5545_ = v_isSharedCheck_5550_;
                                    state = 174;
                                    continue;
                                }
                            } else {
                                v_a_5552_ = crate::leanh::lean_ctor_get(v___x_5542_, 0);
                                crate::leanh::lean_inc(v_a_5552_);
                                crate::leanh::lean_dec_ref_known(v___x_5542_, 1);
                                v___x_5556_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                                v___x_5557_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5556_);
                                crate::leanh::lean_dec_ref(v___x_5557_);
                                state = 176;
                                continue;
                            }
                        }
                    } else {
                        v___x_5558_ =
                            l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31;
                        v___x_5559_ = l___private_Lean_Shell_0__Lean_checkOptArg(
                            v___x_5558_,
                            v_optArg_x3f_4130_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5559_) == 0 {
                            v_a_5560_ = crate::leanh::lean_ctor_get(v___x_5559_, 0);
                            v_isSharedCheck_5610_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5559_)) as u8;
                            if v_isSharedCheck_5610_ == 0 {
                                v___x_5562_ = v___x_5559_;
                                v_isShared_5563_ = v_isSharedCheck_5610_;
                                state = 177;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5560_);
                                crate::leanh::lean_dec(v___x_5559_);
                                v___x_5562_ = crate::leanh::lean_box(0);
                                v_isShared_5563_ = v_isSharedCheck_5610_;
                                state = 177;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_opts_4128_);
                            v_a_5611_ = crate::leanh::lean_ctor_get(v___x_5559_, 0);
                            crate::leanh::lean_inc(v_a_5611_);
                            crate::leanh::lean_dec_ref_known(v___x_5559_, 1);
                            v___x_5615_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                            v___x_5616_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5615_);
                            crate::leanh::lean_dec_ref(v___x_5616_);
                            state = 181;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_optArg_x3f_4130_);
                    v___x_5617_ = lean_internal_set_exit_on_panic(v___x_4329_);
                    v___x_5618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5618_, 0, v_opts_4128_);
                    return v___x_5618_;
                }
            }
            1 => {
                v___x_4133_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4133_);
                return v___x_4134_;
            }
            2 => {
                v___x_4136_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4137_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4136_,
                    );
                crate::leanh::lean_dec_ref(v___x_4137_);
                state = 1;
                continue;
            }
            3 => {
                v___x_4139_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4140_, 0, v___x_4139_);
                return v___x_4140_;
            }
            4 => {
                v___x_4142_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4143_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4143_, 0, v___x_4142_);
                return v___x_4143_;
            }
            5 => {
                v___x_4145_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4146_, 0, v___x_4145_);
                return v___x_4146_;
            }
            6 => {
                v___x_4148_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4149_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4148_,
                    );
                crate::leanh::lean_dec_ref(v___x_4149_);
                state = 5;
                continue;
            }
            7 => {
                v___x_4151_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4152_, 0, v___x_4151_);
                return v___x_4152_;
            }
            8 => {
                v___x_4154_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4155_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4154_,
                    );
                crate::leanh::lean_dec_ref(v___x_4155_);
                state = 7;
                continue;
            }
            9 => {
                v___x_4157_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4158_, 0, v___x_4157_);
                return v___x_4158_;
            }
            10 => {
                v___x_4160_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4161_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4160_,
                    );
                crate::leanh::lean_dec_ref(v___x_4161_);
                state = 9;
                continue;
            }
            11 => {
                v___x_4163_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4164_, 0, v___x_4163_);
                return v___x_4164_;
            }
            12 => {
                v___x_4166_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4167_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4166_,
                    );
                crate::leanh::lean_dec_ref(v___x_4167_);
                state = 11;
                continue;
            }
            13 => {
                v___x_4169_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4170_, 0, v___x_4169_);
                return v___x_4170_;
            }
            14 => {
                v___x_4172_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4173_, 0, v___x_4172_);
                return v___x_4173_;
            }
            15 => {
                v___x_4175_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4176_, 0, v___x_4175_);
                return v___x_4176_;
            }
            16 => {
                v___x_4178_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4179_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4178_,
                    );
                crate::leanh::lean_dec_ref(v___x_4179_);
                state = 15;
                continue;
            }
            17 => {
                v___x_4181_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4182_, 0, v___x_4181_);
                return v___x_4182_;
            }
            18 => {
                v___x_4184_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4185_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4184_,
                    );
                crate::leanh::lean_dec_ref(v___x_4185_);
                state = 17;
                continue;
            }
            19 => {
                v___x_4187_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4188_, 0, v___x_4187_);
                return v___x_4188_;
            }
            20 => {
                v___x_4190_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4191_, 0, v___x_4190_);
                return v___x_4191_;
            }
            21 => {
                v___x_4193_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4194_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4193_,
                    );
                crate::leanh::lean_dec_ref(v___x_4194_);
                state = 20;
                continue;
            }
            22 => {
                v___x_4196_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4197_, 0, v___x_4196_);
                return v___x_4197_;
            }
            23 => {
                v___x_4199_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4200_, 0, v___x_4199_);
                return v___x_4200_;
            }
            24 => {
                v___x_4202_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4203_, 0, v___x_4202_);
                return v___x_4203_;
            }
            25 => {
                v___x_4205_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4206_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4205_,
                    );
                crate::leanh::lean_dec_ref(v___x_4206_);
                state = 24;
                continue;
            }
            26 => {
                v___x_4208_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4209_, 0, v___x_4208_);
                return v___x_4209_;
            }
            27 => {
                v___x_4211_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4212_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4211_,
                    );
                crate::leanh::lean_dec_ref(v___x_4212_);
                state = 26;
                continue;
            }
            28 => {
                v___x_4214_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4215_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4215_, 0, v___x_4214_);
                return v___x_4215_;
            }
            29 => {
                v___x_4217_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4218_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4217_,
                    );
                crate::leanh::lean_dec_ref(v___x_4218_);
                state = 28;
                continue;
            }
            30 => {
                v___x_4220_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4221_, 0, v___x_4220_);
                return v___x_4221_;
            }
            31 => {
                v___x_4223_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4224_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4223_,
                    );
                crate::leanh::lean_dec_ref(v___x_4224_);
                state = 30;
                continue;
            }
            32 => {
                v___x_4226_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
                return v___x_4227_;
            }
            33 => {
                v___x_4229_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4230_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4229_,
                    );
                crate::leanh::lean_dec_ref(v___x_4230_);
                state = 32;
                continue;
            }
            34 => {
                v___x_4233_ = lean_io_error_to_string(v___y_4232_);
                v___x_4234_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4233_,
                    );
                crate::leanh::lean_dec_ref(v___x_4234_);
                state = 33;
                continue;
            }
            35 => {
                v___x_4236_ = 1;
                v___x_4237_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_4236_);
                if crate::leanh::lean_obj_tag(v___x_4237_) == 0 {
                    v_isSharedCheck_4245_ = (!crate::leanh::lean_is_exclusive(v___x_4237_)) as u8;
                    if v_isSharedCheck_4245_ == 0 {
                        v_unused_4246_ = crate::leanh::lean_ctor_get(v___x_4237_, 0);
                        crate::leanh::lean_dec(v_unused_4246_);
                        v___x_4239_ = v___x_4237_;
                        v_isShared_4240_ = v_isSharedCheck_4245_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4237_);
                        v___x_4239_ = crate::leanh::lean_box(0);
                        v_isShared_4240_ = v_isSharedCheck_4245_;
                        state = 36;
                        continue;
                    }
                } else {
                    v_a_4247_ = crate::leanh::lean_ctor_get(v___x_4237_, 0);
                    crate::leanh::lean_inc(v_a_4247_);
                    crate::leanh::lean_dec_ref_known(v___x_4237_, 1);
                    v___x_4248_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                    v___x_4249_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4248_);
                    crate::leanh::lean_dec_ref(v___x_4249_);
                    v___y_4232_ = v_a_4247_;
                    state = 34;
                    continue;
                }
            }
            36 => {
                v___x_4241_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                if v_isShared_4240_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4239_, 1);
                    crate::leanh::lean_ctor_set(v___x_4239_, 0, v___x_4241_);
                    v___x_4243_ = v___x_4239_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
                    v___x_4243_ = v_reuseFailAlloc_4244_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4243_;
            }
            38 => {
                v___x_4251_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0;
                v___x_4252_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4251_,
                    );
                crate::leanh::lean_dec_ref(v___x_4252_);
                state = 35;
                continue;
            }
            39 => {
                v___x_4254_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4255_, 0, v___x_4254_);
                return v___x_4255_;
            }
            40 => {
                v___x_4257_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4258_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4257_,
                    );
                crate::leanh::lean_dec_ref(v___x_4258_);
                state = 39;
                continue;
            }
            41 => {
                v___x_4260_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4261_, 0, v___x_4260_);
                return v___x_4261_;
            }
            42 => {
                v___x_4263_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4264_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4263_,
                    );
                crate::leanh::lean_dec_ref(v___x_4264_);
                state = 41;
                continue;
            }
            43 => {
                v___x_4266_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4267_, 0, v___x_4266_);
                return v___x_4267_;
            }
            44 => {
                v___x_4269_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4270_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4269_,
                    );
                crate::leanh::lean_dec_ref(v___x_4270_);
                state = 43;
                continue;
            }
            45 => {
                v___x_4272_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4273_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4273_, 0, v___x_4272_);
                return v___x_4273_;
            }
            46 => {
                v___x_4275_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4276_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4275_,
                    );
                crate::leanh::lean_dec_ref(v___x_4276_);
                state = 45;
                continue;
            }
            47 => {
                v___x_4278_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4279_, 0, v___x_4278_);
                return v___x_4279_;
            }
            48 => {
                v___x_4281_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4282_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4281_,
                    );
                crate::leanh::lean_dec_ref(v___x_4282_);
                state = 47;
                continue;
            }
            49 => {
                v___x_4284_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4285_, 0, v___x_4284_);
                return v___x_4285_;
            }
            50 => {
                v___x_4287_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4288_, 0, v___x_4287_);
                return v___x_4288_;
            }
            51 => {
                v___x_4290_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4291_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4290_,
                    );
                crate::leanh::lean_dec_ref(v___x_4291_);
                state = 50;
                continue;
            }
            52 => {
                v___x_4293_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4294_, 0, v___x_4293_);
                return v___x_4294_;
            }
            53 => {
                v___x_4296_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4297_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4296_,
                    );
                crate::leanh::lean_dec_ref(v___x_4297_);
                state = 52;
                continue;
            }
            54 => {
                v___x_4299_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4300_, 0, v___x_4299_);
                return v___x_4300_;
            }
            55 => {
                v___x_4302_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4303_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4302_,
                    );
                crate::leanh::lean_dec_ref(v___x_4303_);
                state = 54;
                continue;
            }
            56 => {
                v___x_4305_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4306_, 0, v___x_4305_);
                return v___x_4306_;
            }
            57 => {
                v___x_4308_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4309_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4308_,
                    );
                crate::leanh::lean_dec_ref(v___x_4309_);
                state = 56;
                continue;
            }
            58 => {
                v___x_4311_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4312_, 0, v___x_4311_);
                return v___x_4312_;
            }
            59 => {
                v___x_4314_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4315_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4314_,
                    );
                crate::leanh::lean_dec_ref(v___x_4315_);
                state = 58;
                continue;
            }
            60 => {
                v___x_4317_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4318_, 0, v___x_4317_);
                return v___x_4318_;
            }
            61 => {
                v___x_4320_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4321_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4320_,
                    );
                crate::leanh::lean_dec_ref(v___x_4321_);
                state = 60;
                continue;
            }
            62 => {
                v___x_4323_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_4324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4324_, 0, v___x_4323_);
                return v___x_4324_;
            }
            63 => {
                v___x_4326_ =
                    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0;
                v___x_4327_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4326_,
                    );
                crate::leanh::lean_dec_ref(v___x_4327_);
                state = 62;
                continue;
            }
            64 => {
                v_leanOpts_4404_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                v_forwardedArgs_4405_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                v_component_4406_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_4407_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_4408_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_4409_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_4410_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_4411_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_4412_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_opts_4413_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                v_trustLevel_4414_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_numThreads_4415_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                );
                v_rootDir_x3f_4416_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                v_setupFileName_x3f_4417_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                v_oleanFileName_x3f_4418_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                v_ileanFileName_x3f_4419_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                v_rustFileName_x3f_4420_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                v_bcFileName_x3f_4421_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                v_jsonOutput_4422_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_4423_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                v_printStats_4424_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_4425_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                v_isSharedCheck_4437_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                if v_isSharedCheck_4437_ == 0 {
                    v___x_4427_ = v_opts_4128_;
                    v_isShared_4428_ = v_isSharedCheck_4437_;
                    state = 65;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_errorOnKinds_4423_);
                    crate::leanh::lean_inc(v_bcFileName_x3f_4421_);
                    crate::leanh::lean_inc(v_rustFileName_x3f_4420_);
                    crate::leanh::lean_inc(v_ileanFileName_x3f_4419_);
                    crate::leanh::lean_inc(v_oleanFileName_x3f_4418_);
                    crate::leanh::lean_inc(v_setupFileName_x3f_4417_);
                    crate::leanh::lean_inc(v_rootDir_x3f_4416_);
                    crate::leanh::lean_inc(v_opts_4413_);
                    crate::leanh::lean_inc(v_forwardedArgs_4405_);
                    crate::leanh::lean_inc(v_leanOpts_4404_);
                    crate::leanh::lean_dec(v_opts_4128_);
                    v___x_4427_ = crate::leanh::lean_box(0);
                    v_isShared_4428_ = v_isSharedCheck_4437_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                v___x_4429_ = l_String_toName(v_a_4400_);
                v___x_4430_ = lean_array_push(v_errorOnKinds_4423_, v___x_4429_);
                if v_isShared_4428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4427_, 9, v___x_4430_);
                    v___x_4432_ = v___x_4427_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_4436_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_leanOpts_4404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_forwardedArgs_4405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4436_, 2, v_opts_4413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4436_, 3, v_rootDir_x3f_4416_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4436_,
                        4,
                        v_setupFileName_x3f_4417_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4436_,
                        5,
                        v_oleanFileName_x3f_4418_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4436_,
                        6,
                        v_ileanFileName_x3f_4419_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4436_,
                        7,
                        v_rustFileName_x3f_4420_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4436_, 8, v_bcFileName_x3f_4421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4436_, 9, v___x_4430_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4406_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4407_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4408_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4409_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4410_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4411_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4412_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4414_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4415_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4422_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4424_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4425_,
                    );
                    v___x_4432_ = v_reuseFailAlloc_4436_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                if v_isShared_4403_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4402_, 0, v___x_4432_);
                    v___x_4434_ = v___x_4402_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4432_);
                    v___x_4434_ = v_reuseFailAlloc_4435_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4434_;
            }
            68 => {
                v___x_4441_ = lean_io_error_to_string(v_a_4439_);
                v___x_4442_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4441_,
                    );
                crate::leanh::lean_dec_ref(v___x_4442_);
                state = 40;
                continue;
            }
            69 => {
                v_leanOpts_4451_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                v_forwardedArgs_4452_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                v_component_4453_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_4454_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_4455_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_4456_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_4457_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_4458_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_4459_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_opts_4460_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                v_trustLevel_4461_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_numThreads_4462_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                );
                v_rootDir_x3f_4463_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                v_oleanFileName_x3f_4464_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                v_ileanFileName_x3f_4465_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                v_rustFileName_x3f_4466_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                v_bcFileName_x3f_4467_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                v_jsonOutput_4468_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_4469_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                v_printStats_4470_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_4471_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                v_isSharedCheck_4482_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                if v_isSharedCheck_4482_ == 0 {
                    v_unused_4483_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                    crate::leanh::lean_dec(v_unused_4483_);
                    v___x_4473_ = v_opts_4128_;
                    v_isShared_4474_ = v_isSharedCheck_4482_;
                    state = 70;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_errorOnKinds_4469_);
                    crate::leanh::lean_inc(v_bcFileName_x3f_4467_);
                    crate::leanh::lean_inc(v_rustFileName_x3f_4466_);
                    crate::leanh::lean_inc(v_ileanFileName_x3f_4465_);
                    crate::leanh::lean_inc(v_oleanFileName_x3f_4464_);
                    crate::leanh::lean_inc(v_rootDir_x3f_4463_);
                    crate::leanh::lean_inc(v_opts_4460_);
                    crate::leanh::lean_inc(v_forwardedArgs_4452_);
                    crate::leanh::lean_inc(v_leanOpts_4451_);
                    crate::leanh::lean_dec(v_opts_4128_);
                    v___x_4473_ = crate::leanh::lean_box(0);
                    v_isShared_4474_ = v_isSharedCheck_4482_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                v___x_4475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4475_, 0, v_a_4447_);
                if v_isShared_4474_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4473_, 4, v___x_4475_);
                    v___x_4477_ = v___x_4473_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4481_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_leanOpts_4451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_forwardedArgs_4452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_opts_4460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 3, v_rootDir_x3f_4463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 4, v___x_4475_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4481_,
                        5,
                        v_oleanFileName_x3f_4464_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4481_,
                        6,
                        v_ileanFileName_x3f_4465_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4481_,
                        7,
                        v_rustFileName_x3f_4466_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 8, v_bcFileName_x3f_4467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 9, v_errorOnKinds_4469_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4453_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4454_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4455_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4456_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4457_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4458_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4459_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4461_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4462_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4468_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4470_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4471_,
                    );
                    v___x_4477_ = v_reuseFailAlloc_4481_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_4450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4449_, 0, v___x_4477_);
                    v___x_4479_ = v___x_4449_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_4480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
                    v___x_4479_ = v_reuseFailAlloc_4480_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_4479_;
            }
            73 => {
                v___x_4487_ = lean_io_error_to_string(v_a_4485_);
                v___x_4488_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4487_,
                    );
                crate::leanh::lean_dec_ref(v___x_4488_);
                state = 31;
                continue;
            }
            74 => {
                v___x_4498_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                if v_isShared_4497_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4496_, 1);
                    crate::leanh::lean_ctor_set(v___x_4496_, 0, v___x_4498_);
                    v___x_4500_ = v___x_4496_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
                    v___x_4500_ = v_reuseFailAlloc_4501_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                return v___x_4500_;
            }
            76 => {
                v___x_4506_ = lean_io_error_to_string(v_a_4504_);
                v___x_4507_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4506_,
                    );
                crate::leanh::lean_dec_ref(v___x_4507_);
                state = 42;
                continue;
            }
            77 => {
                v___x_4512_ = lean_io_error_to_string(v_a_4510_);
                v___x_4513_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4512_,
                    );
                crate::leanh::lean_dec_ref(v___x_4513_);
                state = 29;
                continue;
            }
            78 => {
                v___x_4523_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                if v_isShared_4522_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4521_, 1);
                    crate::leanh::lean_ctor_set(v___x_4521_, 0, v___x_4523_);
                    v___x_4525_ = v___x_4521_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_4526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
                    v___x_4525_ = v_reuseFailAlloc_4526_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_4525_;
            }
            80 => {
                v___x_4531_ = lean_io_error_to_string(v_a_4529_);
                v___x_4532_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4531_,
                    );
                crate::leanh::lean_dec_ref(v___x_4532_);
                state = 44;
                continue;
            }
            81 => {
                v___x_4537_ = lean_io_error_to_string(v_a_4535_);
                v___x_4538_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4537_,
                    );
                crate::leanh::lean_dec_ref(v___x_4538_);
                state = 27;
                continue;
            }
            82 => {
                v___x_4548_ = lean_internal_enable_debug(v_a_4544_);
                crate::leanh::lean_dec(v_a_4544_);
                if v_isShared_4547_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4546_, 0, v_opts_4128_);
                    v___x_4550_ = v___x_4546_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_4551_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_opts_4128_);
                    v___x_4550_ = v_reuseFailAlloc_4551_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                return v___x_4550_;
            }
            84 => {
                v___x_4555_ = lean_io_error_to_string(v_a_4553_);
                v___x_4556_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4555_,
                    );
                crate::leanh::lean_dec_ref(v___x_4556_);
                state = 46;
                continue;
            }
            85 => {
                v___x_4584_ = l_Lean_profiler;
                v___x_4585_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_4559_, v___x_4584_, v___x_4387_);
                if v_isShared_4583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4582_, 0, v___x_4585_);
                    v___x_4587_ = v___x_4582_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_4589_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_forwardedArgs_4560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 2, v_opts_4568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 3, v_rootDir_x3f_4571_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4589_,
                        4,
                        v_setupFileName_x3f_4572_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4589_,
                        5,
                        v_oleanFileName_x3f_4573_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4589_,
                        6,
                        v_ileanFileName_x3f_4574_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4589_,
                        7,
                        v_rustFileName_x3f_4575_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 8, v_bcFileName_x3f_4576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 9, v_errorOnKinds_4578_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4561_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4562_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4563_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4564_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4565_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4566_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4567_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4569_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4570_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4577_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4579_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4580_,
                    );
                    v___x_4587_ = v_reuseFailAlloc_4589_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                v___x_4588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4588_, 0, v___x_4587_);
                return v___x_4588_;
            }
            87 => {
                v___x_4615_ = 2;
                if v_isShared_4614_ == 0 {
                    v___x_4617_ = v___x_4613_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_leanOpts_4591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 1, v_forwardedArgs_4592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 2, v_opts_4599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 3, v_rootDir_x3f_4602_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4619_,
                        4,
                        v_setupFileName_x3f_4603_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4619_,
                        5,
                        v_oleanFileName_x3f_4604_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4619_,
                        6,
                        v_ileanFileName_x3f_4605_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4619_,
                        7,
                        v_rustFileName_x3f_4606_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 8, v_bcFileName_x3f_4607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 9, v_errorOnKinds_4609_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4593_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4594_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4595_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4596_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4597_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4598_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4600_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4601_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4608_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4610_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4619_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4611_,
                    );
                    v___x_4617_ = v_reuseFailAlloc_4619_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4617_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                    v___x_4615_,
                );
                v___x_4618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4618_, 0, v___x_4617_);
                return v___x_4618_;
            }
            89 => {
                v___x_4645_ = 1;
                if v_isShared_4644_ == 0 {
                    v___x_4647_ = v___x_4643_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_4649_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_leanOpts_4621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_forwardedArgs_4622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 2, v_opts_4629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 3, v_rootDir_x3f_4632_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4649_,
                        4,
                        v_setupFileName_x3f_4633_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4649_,
                        5,
                        v_oleanFileName_x3f_4634_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4649_,
                        6,
                        v_ileanFileName_x3f_4635_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4649_,
                        7,
                        v_rustFileName_x3f_4636_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 8, v_bcFileName_x3f_4637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 9, v_errorOnKinds_4639_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4623_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4624_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4625_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4626_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4627_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4628_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4630_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4631_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4638_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4640_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4649_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4641_,
                    );
                    v___x_4647_ = v_reuseFailAlloc_4649_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4647_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                    v___x_4645_,
                );
                v___x_4648_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4648_, 0, v___x_4647_);
                return v___x_4648_;
            }
            91 => {
                crate::leanh::lean_inc(v_a_4653_);
                v___x_4679_ =
                    l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_4654_, v_a_4653_);
                if crate::leanh::lean_obj_tag(v___x_4679_) == 0 {
                    v_a_4680_ = crate::leanh::lean_ctor_get(v___x_4679_, 0);
                    v_isSharedCheck_4693_ = (!crate::leanh::lean_is_exclusive(v___x_4679_)) as u8;
                    if v_isSharedCheck_4693_ == 0 {
                        v___x_4682_ = v___x_4679_;
                        v_isShared_4683_ = v_isSharedCheck_4693_;
                        state = 92;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4680_);
                        crate::leanh::lean_dec(v___x_4679_);
                        v___x_4682_ = crate::leanh::lean_box(0);
                        v_isShared_4683_ = v_isSharedCheck_4693_;
                        state = 92;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4677_);
                    crate::leanh::lean_dec_ref(v_errorOnKinds_4673_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_4671_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_4670_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_4669_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_4668_);
                    crate::leanh::lean_dec(v_setupFileName_x3f_4667_);
                    crate::leanh::lean_dec(v_rootDir_x3f_4666_);
                    crate::leanh::lean_dec_ref(v_opts_4663_);
                    crate::leanh::lean_dec_ref(v_forwardedArgs_4655_);
                    crate::leanh::lean_dec(v_a_4653_);
                    v_a_4694_ = crate::leanh::lean_ctor_get(v___x_4679_, 0);
                    crate::leanh::lean_inc(v_a_4694_);
                    crate::leanh::lean_dec_ref_known(v___x_4679_, 1);
                    v___x_4698_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1;
                    v___x_4699_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4698_);
                    crate::leanh::lean_dec_ref(v___x_4699_);
                    state = 95;
                    continue;
                }
            }
            92 => {
                v___x_4684_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9;
                v___x_4685_ = lean_string_append(v___x_4684_, v_a_4653_);
                crate::leanh::lean_dec(v_a_4653_);
                v___x_4686_ = lean_array_push(v_forwardedArgs_4655_, v___x_4685_);
                if v_isShared_4678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4677_, 1, v___x_4686_);
                    crate::leanh::lean_ctor_set(v___x_4677_, 0, v_a_4680_);
                    v___x_4688_ = v___x_4677_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_4692_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4692_, 1, v___x_4686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_opts_4663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4692_, 3, v_rootDir_x3f_4666_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4692_,
                        4,
                        v_setupFileName_x3f_4667_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4692_,
                        5,
                        v_oleanFileName_x3f_4668_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4692_,
                        6,
                        v_ileanFileName_x3f_4669_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4692_,
                        7,
                        v_rustFileName_x3f_4670_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4692_, 8, v_bcFileName_x3f_4671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4692_, 9, v_errorOnKinds_4673_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4656_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4657_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4658_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4659_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4660_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4661_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4662_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4664_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4665_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4672_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4674_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4675_,
                    );
                    v___x_4688_ = v_reuseFailAlloc_4692_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_4683_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4682_, 0, v___x_4688_);
                    v___x_4690_ = v___x_4682_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_4691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
                    v___x_4690_ = v_reuseFailAlloc_4691_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                return v___x_4690_;
            }
            95 => {
                v___x_4696_ = lean_io_error_to_string(v_a_4694_);
                v___x_4697_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4696_,
                    );
                crate::leanh::lean_dec_ref(v___x_4697_);
                state = 25;
                continue;
            }
            96 => {
                v___x_4703_ = lean_io_error_to_string(v_a_4701_);
                v___x_4704_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4703_,
                    );
                crate::leanh::lean_dec_ref(v___x_4704_);
                state = 48;
                continue;
            }
            97 => {
                if v_isShared_4730_ == 0 {
                    v___x_4732_ = v___x_4729_;
                    state = 98;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_leanOpts_4707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 1, v_forwardedArgs_4708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 2, v_opts_4715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 3, v_rootDir_x3f_4718_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4734_,
                        4,
                        v_setupFileName_x3f_4719_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4734_,
                        5,
                        v_oleanFileName_x3f_4720_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4734_,
                        6,
                        v_ileanFileName_x3f_4721_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4734_,
                        7,
                        v_rustFileName_x3f_4722_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 8, v_bcFileName_x3f_4723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 9, v_errorOnKinds_4725_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4709_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4710_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4711_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4712_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4713_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4714_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4716_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4717_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4724_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4726_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4727_,
                    );
                    v___x_4732_ = v_reuseFailAlloc_4734_;
                    state = 98;
                    continue;
                }
            }
            98 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4732_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                    v___x_4379_,
                );
                v___x_4733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4733_, 0, v___x_4732_);
                return v___x_4733_;
            }
            99 => {
                if v_isShared_4759_ == 0 {
                    v___x_4761_ = v___x_4758_;
                    state = 100;
                    continue;
                } else {
                    v_reuseFailAlloc_4763_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_leanOpts_4736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 1, v_forwardedArgs_4737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 2, v_opts_4744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 3, v_rootDir_x3f_4747_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4763_,
                        4,
                        v_setupFileName_x3f_4748_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4763_,
                        5,
                        v_oleanFileName_x3f_4749_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4763_,
                        6,
                        v_ileanFileName_x3f_4750_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4763_,
                        7,
                        v_rustFileName_x3f_4751_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 8, v_bcFileName_x3f_4752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 9, v_errorOnKinds_4754_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4738_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4739_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4740_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4741_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4742_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4743_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4745_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4746_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4753_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4755_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4756_,
                    );
                    v___x_4761_ = v_reuseFailAlloc_4763_;
                    state = 100;
                    continue;
                }
            }
            100 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                    v___x_4377_,
                );
                v___x_4762_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4762_, 0, v___x_4761_);
                return v___x_4762_;
            }
            101 => {
                if v_isShared_4788_ == 0 {
                    v___x_4790_ = v___x_4787_;
                    state = 102;
                    continue;
                } else {
                    v_reuseFailAlloc_4792_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_leanOpts_4765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_forwardedArgs_4766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 2, v_opts_4774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 3, v_rootDir_x3f_4777_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4792_,
                        4,
                        v_setupFileName_x3f_4778_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4792_,
                        5,
                        v_oleanFileName_x3f_4779_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4792_,
                        6,
                        v_ileanFileName_x3f_4780_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4792_,
                        7,
                        v_rustFileName_x3f_4781_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 8, v_bcFileName_x3f_4782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 9, v_errorOnKinds_4784_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4767_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4768_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4769_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4770_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4771_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4772_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4773_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4775_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4776_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4783_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4785_,
                    );
                    v___x_4790_ = v_reuseFailAlloc_4792_;
                    state = 102;
                    continue;
                }
            }
            102 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                    v___x_4375_,
                );
                v___x_4791_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4791_, 0, v___x_4790_);
                return v___x_4791_;
            }
            103 => {
                if v_isShared_4817_ == 0 {
                    v___x_4819_ = v___x_4816_;
                    state = 104;
                    continue;
                } else {
                    v_reuseFailAlloc_4821_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_leanOpts_4794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 1, v_forwardedArgs_4795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 2, v_opts_4803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 3, v_rootDir_x3f_4806_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4821_,
                        4,
                        v_setupFileName_x3f_4807_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4821_,
                        5,
                        v_oleanFileName_x3f_4808_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4821_,
                        6,
                        v_ileanFileName_x3f_4809_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4821_,
                        7,
                        v_rustFileName_x3f_4810_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 8, v_bcFileName_x3f_4811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 9, v_errorOnKinds_4812_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4796_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4797_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4798_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4799_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4800_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4801_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4802_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4804_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4805_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4813_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4821_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4814_,
                    );
                    v___x_4819_ = v_reuseFailAlloc_4821_;
                    state = 104;
                    continue;
                }
            }
            104 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4819_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                    v___x_4373_,
                );
                v___x_4820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4820_, 0, v___x_4819_);
                return v___x_4820_;
            }
            105 => {
                if v_isShared_4845_ == 0 {
                    v___x_4847_ = v___x_4844_;
                    state = 106;
                    continue;
                } else {
                    v_reuseFailAlloc_4849_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_leanOpts_4823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 1, v_forwardedArgs_4824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 2, v_opts_4830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 3, v_rootDir_x3f_4833_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4849_,
                        4,
                        v_setupFileName_x3f_4834_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4849_,
                        5,
                        v_oleanFileName_x3f_4835_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4849_,
                        6,
                        v_ileanFileName_x3f_4836_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4849_,
                        7,
                        v_rustFileName_x3f_4837_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 8, v_bcFileName_x3f_4838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 9, v_errorOnKinds_4840_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4825_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4826_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4827_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4828_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4829_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4831_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4832_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4839_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4841_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4842_,
                    );
                    v___x_4847_ = v_reuseFailAlloc_4849_;
                    state = 106;
                    continue;
                }
            }
            106 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4847_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                    v___x_4371_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4847_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                    v___x_4371_,
                );
                v___x_4848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4848_, 0, v___x_4847_);
                return v___x_4848_;
            }
            107 => {
                if v_isShared_4874_ == 0 {
                    v___x_4876_ = v___x_4873_;
                    state = 108;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_leanOpts_4851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 1, v_forwardedArgs_4852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 2, v_opts_4859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 3, v_rootDir_x3f_4862_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4878_,
                        4,
                        v_setupFileName_x3f_4863_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4878_,
                        5,
                        v_oleanFileName_x3f_4864_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4878_,
                        6,
                        v_ileanFileName_x3f_4865_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4878_,
                        7,
                        v_rustFileName_x3f_4866_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 8, v_bcFileName_x3f_4867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 9, v_errorOnKinds_4869_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4853_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4854_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4855_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4856_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4857_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4858_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4860_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4861_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4868_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4870_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4878_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4871_,
                    );
                    v___x_4876_ = v_reuseFailAlloc_4878_;
                    state = 108;
                    continue;
                }
            }
            108 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4876_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                    v___x_4369_,
                );
                v___x_4877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4877_, 0, v___x_4876_);
                return v___x_4877_;
            }
            109 => {
                if v_isShared_4903_ == 0 {
                    v___x_4905_ = v___x_4902_;
                    state = 110;
                    continue;
                } else {
                    v_reuseFailAlloc_4907_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_leanOpts_4880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 1, v_forwardedArgs_4881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 2, v_opts_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 3, v_rootDir_x3f_4891_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4907_,
                        4,
                        v_setupFileName_x3f_4892_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4907_,
                        5,
                        v_oleanFileName_x3f_4893_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4907_,
                        6,
                        v_ileanFileName_x3f_4894_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4907_,
                        7,
                        v_rustFileName_x3f_4895_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 8, v_bcFileName_x3f_4896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 9, v_errorOnKinds_4898_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4882_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4883_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4884_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4885_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4886_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4887_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4889_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4890_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4897_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4899_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4907_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4900_,
                    );
                    v___x_4905_ = v_reuseFailAlloc_4907_;
                    state = 110;
                    continue;
                }
            }
            110 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4905_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                    v___x_4367_,
                );
                v___x_4906_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4906_, 0, v___x_4905_);
                return v___x_4906_;
            }
            111 => {
                v___x_4934_ = l___private_Lean_Shell_0__Lean_verbose;
                v___x_4935_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_4909_, v___x_4934_, v___x_4363_);
                if v_isShared_4933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4932_, 0, v___x_4935_);
                    v___x_4937_ = v___x_4932_;
                    state = 112;
                    continue;
                } else {
                    v_reuseFailAlloc_4939_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_forwardedArgs_4910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 2, v_opts_4918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 3, v_rootDir_x3f_4921_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4939_,
                        4,
                        v_setupFileName_x3f_4922_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4939_,
                        5,
                        v_oleanFileName_x3f_4923_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4939_,
                        6,
                        v_ileanFileName_x3f_4924_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4939_,
                        7,
                        v_rustFileName_x3f_4925_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 8, v_bcFileName_x3f_4926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 9, v_errorOnKinds_4928_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4911_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4912_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4913_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4914_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4915_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4916_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4917_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_4919_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4920_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4927_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4929_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4939_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4930_,
                    );
                    v___x_4937_ = v_reuseFailAlloc_4939_;
                    state = 112;
                    continue;
                }
            }
            112 => {
                v___x_4938_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4938_, 0, v___x_4937_);
                return v___x_4938_;
            }
            113 => {
                v___x_4947_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4948_ = lean_string_utf8_byte_size(v_a_4943_);
                crate::leanh::lean_inc(v_a_4943_);
                v___x_4949_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4949_, 0, v_a_4943_);
                crate::leanh::lean_ctor_set(v___x_4949_, 1, v___x_4947_);
                crate::leanh::lean_ctor_set(v___x_4949_, 2, v___x_4948_);
                v___x_4950_ = l_String_Slice_toNat_x3f(v___x_4949_);
                crate::leanh::lean_dec_ref_known(v___x_4949_, 3);
                if crate::leanh::lean_obj_tag(v___x_4950_) == 1 {
                    v_val_4951_ = crate::leanh::lean_ctor_get(v___x_4950_, 0);
                    crate::leanh::lean_inc(v_val_4951_);
                    crate::leanh::lean_dec_ref_known(v___x_4950_, 1);
                    v___x_4952_ = crate::leanh::lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
                    v___x_4953_ = lean_nat_dec_lt(v_val_4951_, v___x_4952_);
                    if v___x_4953_ == 0 {
                        crate::leanh::lean_dec(v_val_4951_);
                        crate::leanh::lean_del_object(v___x_4945_);
                        crate::leanh::lean_dec(v_a_4943_);
                        crate::leanh::lean_dec_ref(v_opts_4128_);
                        v___x_4954_ =
                            l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11;
                        v___x_4955_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4954_);
                        crate::leanh::lean_dec_ref(v___x_4955_);
                        state = 23;
                        continue;
                    } else {
                        v_leanOpts_4956_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                        v_forwardedArgs_4957_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                        v_component_4958_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        );
                        v_printPrefix_4959_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        );
                        v_printLibDir_4960_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10)
                                as u32,
                        );
                        v_useStdin_4961_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11)
                                as u32,
                        );
                        v_onlyDeps_4962_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12)
                                as u32,
                        );
                        v_onlySrcDeps_4963_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13)
                                as u32,
                        );
                        v_depsJson_4964_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14)
                                as u32,
                        );
                        v_opts_4965_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                        v_numThreads_4966_ = crate::leanh::lean_ctor_get_uint32(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        );
                        v_rootDir_x3f_4967_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                        v_setupFileName_x3f_4968_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                        v_oleanFileName_x3f_4969_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                        v_ileanFileName_x3f_4970_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                        v_rustFileName_x3f_4971_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                        v_bcFileName_x3f_4972_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                        v_jsonOutput_4973_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15)
                                as u32,
                        );
                        v_errorOnKinds_4974_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                        v_printStats_4975_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16)
                                as u32,
                        );
                        v_run_4976_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17)
                                as u32,
                        );
                        v_isSharedCheck_4990_ =
                            (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                        if v_isSharedCheck_4990_ == 0 {
                            v___x_4978_ = v_opts_4128_;
                            v_isShared_4979_ = v_isSharedCheck_4990_;
                            state = 114;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_errorOnKinds_4974_);
                            crate::leanh::lean_inc(v_bcFileName_x3f_4972_);
                            crate::leanh::lean_inc(v_rustFileName_x3f_4971_);
                            crate::leanh::lean_inc(v_ileanFileName_x3f_4970_);
                            crate::leanh::lean_inc(v_oleanFileName_x3f_4969_);
                            crate::leanh::lean_inc(v_setupFileName_x3f_4968_);
                            crate::leanh::lean_inc(v_rootDir_x3f_4967_);
                            crate::leanh::lean_inc(v_opts_4965_);
                            crate::leanh::lean_inc(v_forwardedArgs_4957_);
                            crate::leanh::lean_inc(v_leanOpts_4956_);
                            crate::leanh::lean_dec(v_opts_4128_);
                            v___x_4978_ = crate::leanh::lean_box(0);
                            v_isShared_4979_ = v_isSharedCheck_4990_;
                            state = 114;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4950_);
                    crate::leanh::lean_del_object(v___x_4945_);
                    crate::leanh::lean_dec(v_a_4943_);
                    crate::leanh::lean_dec_ref(v_opts_4128_);
                    v___x_4991_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13;
                    v___x_4992_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_4991_);
                    crate::leanh::lean_dec_ref(v___x_4992_);
                    state = 22;
                    continue;
                }
            }
            114 => {
                v___x_4980_ = lean_uint32_of_nat(v_val_4951_);
                crate::leanh::lean_dec(v_val_4951_);
                v___x_4981_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12;
                v___x_4982_ = lean_string_append(v___x_4981_, v_a_4943_);
                crate::leanh::lean_dec(v_a_4943_);
                v___x_4983_ = lean_array_push(v_forwardedArgs_4957_, v___x_4982_);
                if v_isShared_4979_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4978_, 1, v___x_4983_);
                    v___x_4985_ = v___x_4978_;
                    state = 115;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_leanOpts_4956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 1, v___x_4983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_opts_4965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 3, v_rootDir_x3f_4967_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4989_,
                        4,
                        v_setupFileName_x3f_4968_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4989_,
                        5,
                        v_oleanFileName_x3f_4969_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4989_,
                        6,
                        v_ileanFileName_x3f_4970_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4989_,
                        7,
                        v_rustFileName_x3f_4971_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 8, v_bcFileName_x3f_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 9, v_errorOnKinds_4974_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_4958_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_4959_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_4960_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_4961_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_4962_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_4963_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_4964_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_4966_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_4973_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_4975_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_4976_,
                    );
                    v___x_4985_ = v_reuseFailAlloc_4989_;
                    state = 115;
                    continue;
                }
            }
            115 => {
                crate::leanh::lean_ctor_set_uint32(
                    v___x_4985_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_4980_,
                );
                if v_isShared_4946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4945_, 0, v___x_4985_);
                    v___x_4987_ = v___x_4945_;
                    state = 116;
                    continue;
                } else {
                    v_reuseFailAlloc_4988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
                    v___x_4987_ = v_reuseFailAlloc_4988_;
                    state = 116;
                    continue;
                }
            }
            116 => {
                return v___x_4987_;
            }
            117 => {
                v___x_4996_ = lean_io_error_to_string(v_a_4994_);
                v___x_4997_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_4996_,
                    );
                crate::leanh::lean_dec_ref(v___x_4997_);
                state = 21;
                continue;
            }
            118 => {
                v___x_5006_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5007_ = lean_string_utf8_byte_size(v_a_5002_);
                crate::leanh::lean_inc(v_a_5002_);
                v___x_5008_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5008_, 0, v_a_5002_);
                crate::leanh::lean_ctor_set(v___x_5008_, 1, v___x_5006_);
                crate::leanh::lean_ctor_set(v___x_5008_, 2, v___x_5007_);
                v___x_5009_ = l_String_Slice_toNat_x3f(v___x_5008_);
                crate::leanh::lean_dec_ref_known(v___x_5008_, 3);
                if crate::leanh::lean_obj_tag(v___x_5009_) == 1 {
                    v_val_5010_ = crate::leanh::lean_ctor_get(v___x_5009_, 0);
                    crate::leanh::lean_inc(v_val_5010_);
                    crate::leanh::lean_dec_ref_known(v___x_5009_, 1);
                    v_leanOpts_5011_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                    v_forwardedArgs_5012_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                    v_component_5013_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                    );
                    v_printPrefix_5014_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                    );
                    v_printLibDir_5015_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                    );
                    v_useStdin_5016_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                    );
                    v_onlyDeps_5017_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                    );
                    v_onlySrcDeps_5018_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                    );
                    v_depsJson_5019_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                    );
                    v_opts_5020_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                    v_trustLevel_5021_ = crate::leanh::lean_ctor_get_uint32(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_numThreads_5022_ = crate::leanh::lean_ctor_get_uint32(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                    );
                    v_rootDir_x3f_5023_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                    v_setupFileName_x3f_5024_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                    v_oleanFileName_x3f_5025_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                    v_ileanFileName_x3f_5026_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                    v_rustFileName_x3f_5027_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                    v_bcFileName_x3f_5028_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                    v_jsonOutput_5029_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                    );
                    v_errorOnKinds_5030_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                    v_printStats_5031_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                    );
                    v_run_5032_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                    );
                    v_isSharedCheck_5047_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                    if v_isSharedCheck_5047_ == 0 {
                        v___x_5034_ = v_opts_4128_;
                        v_isShared_5035_ = v_isSharedCheck_5047_;
                        state = 119;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_errorOnKinds_5030_);
                        crate::leanh::lean_inc(v_bcFileName_x3f_5028_);
                        crate::leanh::lean_inc(v_rustFileName_x3f_5027_);
                        crate::leanh::lean_inc(v_ileanFileName_x3f_5026_);
                        crate::leanh::lean_inc(v_oleanFileName_x3f_5025_);
                        crate::leanh::lean_inc(v_setupFileName_x3f_5024_);
                        crate::leanh::lean_inc(v_rootDir_x3f_5023_);
                        crate::leanh::lean_inc(v_opts_5020_);
                        crate::leanh::lean_inc(v_forwardedArgs_5012_);
                        crate::leanh::lean_inc(v_leanOpts_5011_);
                        crate::leanh::lean_dec(v_opts_4128_);
                        v___x_5034_ = crate::leanh::lean_box(0);
                        v_isShared_5035_ = v_isSharedCheck_5047_;
                        state = 119;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5009_);
                    crate::leanh::lean_del_object(v___x_5004_);
                    crate::leanh::lean_dec(v_a_5002_);
                    crate::leanh::lean_dec_ref(v_opts_4128_);
                    v___x_5048_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16;
                    v___x_5049_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5048_);
                    crate::leanh::lean_dec_ref(v___x_5049_);
                    state = 49;
                    continue;
                }
            }
            119 => {
                v___x_5036_ = l___private_Lean_Shell_0__Lean_timeout;
                v___x_5037_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_leanOpts_5011_, v___x_5036_, v_val_5010_);
                v___x_5038_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15;
                v___x_5039_ = lean_string_append(v___x_5038_, v_a_5002_);
                crate::leanh::lean_dec(v_a_5002_);
                v___x_5040_ = lean_array_push(v_forwardedArgs_5012_, v___x_5039_);
                if v_isShared_5035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5034_, 1, v___x_5040_);
                    crate::leanh::lean_ctor_set(v___x_5034_, 0, v___x_5037_);
                    v___x_5042_ = v___x_5034_;
                    state = 120;
                    continue;
                } else {
                    v_reuseFailAlloc_5046_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___x_5040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 2, v_opts_5020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 3, v_rootDir_x3f_5023_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5046_,
                        4,
                        v_setupFileName_x3f_5024_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5046_,
                        5,
                        v_oleanFileName_x3f_5025_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5046_,
                        6,
                        v_ileanFileName_x3f_5026_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5046_,
                        7,
                        v_rustFileName_x3f_5027_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 8, v_bcFileName_x3f_5028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 9, v_errorOnKinds_5030_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5013_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5014_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5015_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5016_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5017_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5018_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5019_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5021_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5022_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5029_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5031_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5046_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5032_,
                    );
                    v___x_5042_ = v_reuseFailAlloc_5046_;
                    state = 120;
                    continue;
                }
            }
            120 => {
                if v_isShared_5005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5004_, 0, v___x_5042_);
                    v___x_5044_ = v___x_5004_;
                    state = 121;
                    continue;
                } else {
                    v_reuseFailAlloc_5045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5042_);
                    v___x_5044_ = v_reuseFailAlloc_5045_;
                    state = 121;
                    continue;
                }
            }
            121 => {
                return v___x_5044_;
            }
            122 => {
                v___x_5053_ = lean_io_error_to_string(v_a_5051_);
                v___x_5054_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5053_,
                    );
                crate::leanh::lean_dec_ref(v___x_5054_);
                state = 51;
                continue;
            }
            123 => {
                v___x_5063_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5064_ = lean_string_utf8_byte_size(v_a_5059_);
                crate::leanh::lean_inc(v_a_5059_);
                v___x_5065_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5065_, 0, v_a_5059_);
                crate::leanh::lean_ctor_set(v___x_5065_, 1, v___x_5063_);
                crate::leanh::lean_ctor_set(v___x_5065_, 2, v___x_5064_);
                v___x_5066_ = l_String_Slice_toNat_x3f(v___x_5065_);
                crate::leanh::lean_dec_ref_known(v___x_5065_, 3);
                if crate::leanh::lean_obj_tag(v___x_5066_) == 1 {
                    v_val_5067_ = crate::leanh::lean_ctor_get(v___x_5066_, 0);
                    crate::leanh::lean_inc(v_val_5067_);
                    crate::leanh::lean_dec_ref_known(v___x_5066_, 1);
                    v_leanOpts_5068_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                    v_forwardedArgs_5069_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                    v_component_5070_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                    );
                    v_printPrefix_5071_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                    );
                    v_printLibDir_5072_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                    );
                    v_useStdin_5073_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                    );
                    v_onlyDeps_5074_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                    );
                    v_onlySrcDeps_5075_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                    );
                    v_depsJson_5076_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                    );
                    v_opts_5077_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                    v_trustLevel_5078_ = crate::leanh::lean_ctor_get_uint32(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_numThreads_5079_ = crate::leanh::lean_ctor_get_uint32(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                    );
                    v_rootDir_x3f_5080_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                    v_setupFileName_x3f_5081_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                    v_oleanFileName_x3f_5082_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                    v_ileanFileName_x3f_5083_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                    v_rustFileName_x3f_5084_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                    v_bcFileName_x3f_5085_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                    v_jsonOutput_5086_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                    );
                    v_errorOnKinds_5087_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                    v_printStats_5088_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                    );
                    v_run_5089_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_4128_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                    );
                    v_isSharedCheck_5104_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                    if v_isSharedCheck_5104_ == 0 {
                        v___x_5091_ = v_opts_4128_;
                        v_isShared_5092_ = v_isSharedCheck_5104_;
                        state = 124;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_errorOnKinds_5087_);
                        crate::leanh::lean_inc(v_bcFileName_x3f_5085_);
                        crate::leanh::lean_inc(v_rustFileName_x3f_5084_);
                        crate::leanh::lean_inc(v_ileanFileName_x3f_5083_);
                        crate::leanh::lean_inc(v_oleanFileName_x3f_5082_);
                        crate::leanh::lean_inc(v_setupFileName_x3f_5081_);
                        crate::leanh::lean_inc(v_rootDir_x3f_5080_);
                        crate::leanh::lean_inc(v_opts_5077_);
                        crate::leanh::lean_inc(v_forwardedArgs_5069_);
                        crate::leanh::lean_inc(v_leanOpts_5068_);
                        crate::leanh::lean_dec(v_opts_4128_);
                        v___x_5091_ = crate::leanh::lean_box(0);
                        v_isShared_5092_ = v_isSharedCheck_5104_;
                        state = 124;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5066_);
                    crate::leanh::lean_del_object(v___x_5061_);
                    crate::leanh::lean_dec(v_a_5059_);
                    crate::leanh::lean_dec_ref(v_opts_4128_);
                    v___x_5105_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19;
                    v___x_5106_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5105_);
                    crate::leanh::lean_dec_ref(v___x_5106_);
                    state = 19;
                    continue;
                }
            }
            124 => {
                v___x_5093_ = l___private_Lean_Shell_0__Lean_maxMemory;
                v___x_5094_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_leanOpts_5068_, v___x_5093_, v_val_5067_);
                v___x_5095_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18;
                v___x_5096_ = lean_string_append(v___x_5095_, v_a_5059_);
                crate::leanh::lean_dec(v_a_5059_);
                v___x_5097_ = lean_array_push(v_forwardedArgs_5069_, v___x_5096_);
                if v_isShared_5092_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5091_, 1, v___x_5097_);
                    crate::leanh::lean_ctor_set(v___x_5091_, 0, v___x_5094_);
                    v___x_5099_ = v___x_5091_;
                    state = 125;
                    continue;
                } else {
                    v_reuseFailAlloc_5103_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 1, v___x_5097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_opts_5077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_rootDir_x3f_5080_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5103_,
                        4,
                        v_setupFileName_x3f_5081_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5103_,
                        5,
                        v_oleanFileName_x3f_5082_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5103_,
                        6,
                        v_ileanFileName_x3f_5083_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5103_,
                        7,
                        v_rustFileName_x3f_5084_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 8, v_bcFileName_x3f_5085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 9, v_errorOnKinds_5087_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5070_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5071_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5072_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5073_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5074_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5075_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5076_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5078_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5079_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5086_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5088_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5089_,
                    );
                    v___x_5099_ = v_reuseFailAlloc_5103_;
                    state = 125;
                    continue;
                }
            }
            125 => {
                if v_isShared_5062_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5061_, 0, v___x_5099_);
                    v___x_5101_ = v___x_5061_;
                    state = 126;
                    continue;
                } else {
                    v_reuseFailAlloc_5102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5099_);
                    v___x_5101_ = v_reuseFailAlloc_5102_;
                    state = 126;
                    continue;
                }
            }
            126 => {
                return v___x_5101_;
            }
            127 => {
                v___x_5110_ = lean_io_error_to_string(v_a_5108_);
                v___x_5111_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5110_,
                    );
                crate::leanh::lean_dec_ref(v___x_5111_);
                state = 18;
                continue;
            }
            128 => {
                v_leanOpts_5120_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                v_forwardedArgs_5121_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                v_component_5122_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_5123_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_5124_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_5125_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_5126_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_5127_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_5128_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_opts_5129_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                v_trustLevel_5130_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_numThreads_5131_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                );
                v_setupFileName_x3f_5132_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                v_oleanFileName_x3f_5133_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                v_ileanFileName_x3f_5134_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                v_rustFileName_x3f_5135_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                v_bcFileName_x3f_5136_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                v_jsonOutput_5137_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_5138_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                v_printStats_5139_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_5140_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                v_isSharedCheck_5154_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                if v_isSharedCheck_5154_ == 0 {
                    v_unused_5155_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                    crate::leanh::lean_dec(v_unused_5155_);
                    v___x_5142_ = v_opts_4128_;
                    v_isShared_5143_ = v_isSharedCheck_5154_;
                    state = 129;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_errorOnKinds_5138_);
                    crate::leanh::lean_inc(v_bcFileName_x3f_5136_);
                    crate::leanh::lean_inc(v_rustFileName_x3f_5135_);
                    crate::leanh::lean_inc(v_ileanFileName_x3f_5134_);
                    crate::leanh::lean_inc(v_oleanFileName_x3f_5133_);
                    crate::leanh::lean_inc(v_setupFileName_x3f_5132_);
                    crate::leanh::lean_inc(v_opts_5129_);
                    crate::leanh::lean_inc(v_forwardedArgs_5121_);
                    crate::leanh::lean_inc(v_leanOpts_5120_);
                    crate::leanh::lean_dec(v_opts_4128_);
                    v___x_5142_ = crate::leanh::lean_box(0);
                    v_isShared_5143_ = v_isSharedCheck_5154_;
                    state = 129;
                    continue;
                }
            }
            129 => {
                v___x_5144_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21;
                v___x_5145_ = lean_string_append(v___x_5144_, v_a_5116_);
                v___x_5146_ = lean_array_push(v_forwardedArgs_5121_, v___x_5145_);
                v___x_5147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5147_, 0, v_a_5116_);
                if v_isShared_5143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5142_, 3, v___x_5147_);
                    crate::leanh::lean_ctor_set(v___x_5142_, 1, v___x_5146_);
                    v___x_5149_ = v___x_5142_;
                    state = 130;
                    continue;
                } else {
                    v_reuseFailAlloc_5153_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_leanOpts_5120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 1, v___x_5146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 2, v_opts_5129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 3, v___x_5147_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5153_,
                        4,
                        v_setupFileName_x3f_5132_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5153_,
                        5,
                        v_oleanFileName_x3f_5133_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5153_,
                        6,
                        v_ileanFileName_x3f_5134_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5153_,
                        7,
                        v_rustFileName_x3f_5135_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 8, v_bcFileName_x3f_5136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 9, v_errorOnKinds_5138_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5122_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5123_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5124_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5125_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5126_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5127_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5128_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5130_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5131_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5137_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5139_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5140_,
                    );
                    v___x_5149_ = v_reuseFailAlloc_5153_;
                    state = 130;
                    continue;
                }
            }
            130 => {
                if v_isShared_5119_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5118_, 0, v___x_5149_);
                    v___x_5151_ = v___x_5118_;
                    state = 131;
                    continue;
                } else {
                    v_reuseFailAlloc_5152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5149_);
                    v___x_5151_ = v_reuseFailAlloc_5152_;
                    state = 131;
                    continue;
                }
            }
            131 => {
                return v___x_5151_;
            }
            132 => {
                v___x_5159_ = lean_io_error_to_string(v_a_5157_);
                v___x_5160_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5159_,
                    );
                crate::leanh::lean_dec_ref(v___x_5160_);
                state = 53;
                continue;
            }
            133 => {
                v_leanOpts_5169_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                v_forwardedArgs_5170_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                v_component_5171_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_5172_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_5173_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_5174_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_5175_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_5176_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_5177_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_opts_5178_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                v_trustLevel_5179_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_numThreads_5180_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                );
                v_rootDir_x3f_5181_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                v_setupFileName_x3f_5182_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                v_oleanFileName_x3f_5183_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                v_rustFileName_x3f_5184_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                v_bcFileName_x3f_5185_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                v_jsonOutput_5186_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_5187_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                v_printStats_5188_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_5189_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                v_isSharedCheck_5200_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                if v_isSharedCheck_5200_ == 0 {
                    v_unused_5201_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                    crate::leanh::lean_dec(v_unused_5201_);
                    v___x_5191_ = v_opts_4128_;
                    v_isShared_5192_ = v_isSharedCheck_5200_;
                    state = 134;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_errorOnKinds_5187_);
                    crate::leanh::lean_inc(v_bcFileName_x3f_5185_);
                    crate::leanh::lean_inc(v_rustFileName_x3f_5184_);
                    crate::leanh::lean_inc(v_oleanFileName_x3f_5183_);
                    crate::leanh::lean_inc(v_setupFileName_x3f_5182_);
                    crate::leanh::lean_inc(v_rootDir_x3f_5181_);
                    crate::leanh::lean_inc(v_opts_5178_);
                    crate::leanh::lean_inc(v_forwardedArgs_5170_);
                    crate::leanh::lean_inc(v_leanOpts_5169_);
                    crate::leanh::lean_dec(v_opts_4128_);
                    v___x_5191_ = crate::leanh::lean_box(0);
                    v_isShared_5192_ = v_isSharedCheck_5200_;
                    state = 134;
                    continue;
                }
            }
            134 => {
                v___x_5193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5193_, 0, v_a_5165_);
                if v_isShared_5192_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5191_, 6, v___x_5193_);
                    v___x_5195_ = v___x_5191_;
                    state = 135;
                    continue;
                } else {
                    v_reuseFailAlloc_5199_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_leanOpts_5169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5199_, 1, v_forwardedArgs_5170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5199_, 2, v_opts_5178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5199_, 3, v_rootDir_x3f_5181_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5199_,
                        4,
                        v_setupFileName_x3f_5182_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5199_,
                        5,
                        v_oleanFileName_x3f_5183_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5199_, 6, v___x_5193_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5199_,
                        7,
                        v_rustFileName_x3f_5184_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5199_, 8, v_bcFileName_x3f_5185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5199_, 9, v_errorOnKinds_5187_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5171_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5172_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5173_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5174_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5175_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5176_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5177_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5179_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5180_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5186_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5188_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5189_,
                    );
                    v___x_5195_ = v_reuseFailAlloc_5199_;
                    state = 135;
                    continue;
                }
            }
            135 => {
                if v_isShared_5168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5167_, 0, v___x_5195_);
                    v___x_5197_ = v___x_5167_;
                    state = 136;
                    continue;
                } else {
                    v_reuseFailAlloc_5198_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 0, v___x_5195_);
                    v___x_5197_ = v_reuseFailAlloc_5198_;
                    state = 136;
                    continue;
                }
            }
            136 => {
                return v___x_5197_;
            }
            137 => {
                v___x_5205_ = lean_io_error_to_string(v_a_5203_);
                v___x_5206_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5205_,
                    );
                crate::leanh::lean_dec_ref(v___x_5206_);
                state = 16;
                continue;
            }
            138 => {
                v_leanOpts_5215_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                v_forwardedArgs_5216_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                v_component_5217_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_5218_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_5219_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_5220_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_5221_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_5222_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_5223_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_opts_5224_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                v_trustLevel_5225_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_numThreads_5226_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                );
                v_rootDir_x3f_5227_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                v_setupFileName_x3f_5228_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                v_ileanFileName_x3f_5229_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                v_rustFileName_x3f_5230_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                v_bcFileName_x3f_5231_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                v_jsonOutput_5232_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_5233_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                v_printStats_5234_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_5235_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                v_isSharedCheck_5246_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                if v_isSharedCheck_5246_ == 0 {
                    v_unused_5247_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                    crate::leanh::lean_dec(v_unused_5247_);
                    v___x_5237_ = v_opts_4128_;
                    v_isShared_5238_ = v_isSharedCheck_5246_;
                    state = 139;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_errorOnKinds_5233_);
                    crate::leanh::lean_inc(v_bcFileName_x3f_5231_);
                    crate::leanh::lean_inc(v_rustFileName_x3f_5230_);
                    crate::leanh::lean_inc(v_ileanFileName_x3f_5229_);
                    crate::leanh::lean_inc(v_setupFileName_x3f_5228_);
                    crate::leanh::lean_inc(v_rootDir_x3f_5227_);
                    crate::leanh::lean_inc(v_opts_5224_);
                    crate::leanh::lean_inc(v_forwardedArgs_5216_);
                    crate::leanh::lean_inc(v_leanOpts_5215_);
                    crate::leanh::lean_dec(v_opts_4128_);
                    v___x_5237_ = crate::leanh::lean_box(0);
                    v_isShared_5238_ = v_isSharedCheck_5246_;
                    state = 139;
                    continue;
                }
            }
            139 => {
                v___x_5239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5239_, 0, v_a_5211_);
                if v_isShared_5238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5237_, 5, v___x_5239_);
                    v___x_5241_ = v___x_5237_;
                    state = 140;
                    continue;
                } else {
                    v_reuseFailAlloc_5245_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_leanOpts_5215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 1, v_forwardedArgs_5216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 2, v_opts_5224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 3, v_rootDir_x3f_5227_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5245_,
                        4,
                        v_setupFileName_x3f_5228_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 5, v___x_5239_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5245_,
                        6,
                        v_ileanFileName_x3f_5229_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5245_,
                        7,
                        v_rustFileName_x3f_5230_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 8, v_bcFileName_x3f_5231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 9, v_errorOnKinds_5233_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5217_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5218_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5219_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5220_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5221_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5222_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5223_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5225_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5226_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5232_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5234_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5235_,
                    );
                    v___x_5241_ = v_reuseFailAlloc_5245_;
                    state = 140;
                    continue;
                }
            }
            140 => {
                if v_isShared_5214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5213_, 0, v___x_5241_);
                    v___x_5243_ = v___x_5213_;
                    state = 141;
                    continue;
                } else {
                    v_reuseFailAlloc_5244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5241_);
                    v___x_5243_ = v_reuseFailAlloc_5244_;
                    state = 141;
                    continue;
                }
            }
            141 => {
                return v___x_5243_;
            }
            142 => {
                v___x_5251_ = lean_io_error_to_string(v_a_5249_);
                v___x_5252_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5251_,
                    );
                crate::leanh::lean_dec_ref(v___x_5252_);
                state = 55;
                continue;
            }
            143 => {
                v___x_5279_ = l_Lean_Compiler_compiler_postponeCompile;
                v___x_5280_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_5255_, v___x_5279_, v___x_4349_);
                if v_isShared_5278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5277_, 0, v___x_5280_);
                    v___x_5282_ = v___x_5277_;
                    state = 144;
                    continue;
                } else {
                    v_reuseFailAlloc_5284_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 1, v_forwardedArgs_5256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 2, v_opts_5264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 3, v_rootDir_x3f_5267_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5284_,
                        4,
                        v_setupFileName_x3f_5268_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5284_,
                        5,
                        v_oleanFileName_x3f_5269_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5284_,
                        6,
                        v_ileanFileName_x3f_5270_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5284_,
                        7,
                        v_rustFileName_x3f_5271_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 8, v_bcFileName_x3f_5272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 9, v_errorOnKinds_5274_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5257_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5258_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5259_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5260_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5261_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5262_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5263_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5265_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5266_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5273_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5284_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5275_,
                    );
                    v___x_5282_ = v_reuseFailAlloc_5284_;
                    state = 144;
                    continue;
                }
            }
            144 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5282_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                    v___x_4351_,
                );
                v___x_5283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5283_, 0, v___x_5282_);
                return v___x_5283_;
            }
            145 => {
                if v_isShared_5309_ == 0 {
                    v___x_5311_ = v___x_5308_;
                    state = 146;
                    continue;
                } else {
                    v_reuseFailAlloc_5313_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 0, v_leanOpts_5286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 1, v_forwardedArgs_5287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 2, v_opts_5294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 3, v_rootDir_x3f_5297_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5313_,
                        4,
                        v_setupFileName_x3f_5298_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5313_,
                        5,
                        v_oleanFileName_x3f_5299_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5313_,
                        6,
                        v_ileanFileName_x3f_5300_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5313_,
                        7,
                        v_rustFileName_x3f_5301_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 8, v_bcFileName_x3f_5302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 9, v_errorOnKinds_5304_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5288_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5289_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5290_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5291_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5292_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5293_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5295_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5296_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5303_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5305_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5306_,
                    );
                    v___x_5311_ = v_reuseFailAlloc_5313_;
                    state = 146;
                    continue;
                }
            }
            146 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5311_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                    v___x_4349_,
                );
                v___x_5312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5312_, 0, v___x_5311_);
                return v___x_5312_;
            }
            147 => {
                v___x_5321_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5322_ = lean_string_utf8_byte_size(v_a_5317_);
                crate::leanh::lean_inc(v_a_5317_);
                v___x_5323_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5323_, 0, v_a_5317_);
                crate::leanh::lean_ctor_set(v___x_5323_, 1, v___x_5321_);
                crate::leanh::lean_ctor_set(v___x_5323_, 2, v___x_5322_);
                v___x_5324_ = l_String_Slice_toNat_x3f(v___x_5323_);
                crate::leanh::lean_dec_ref_known(v___x_5323_, 3);
                if crate::leanh::lean_obj_tag(v___x_5324_) == 1 {
                    v_val_5325_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                    crate::leanh::lean_inc(v_val_5325_);
                    crate::leanh::lean_dec_ref_known(v___x_5324_, 1);
                    v___x_5326_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5327_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_5328_ = lean_nat_shiftr(v_val_5325_, v___x_5327_);
                    crate::leanh::lean_dec(v_val_5325_);
                    v___x_5329_ = lean_nat_mul(v___x_5328_, v___x_5326_);
                    crate::leanh::lean_dec(v___x_5328_);
                    v___x_5330_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_5331_ = lean_nat_mul(v___x_5329_, v___x_5330_);
                    crate::leanh::lean_dec(v___x_5329_);
                    v___x_5332_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once
                        ),
                        _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25,
                    );
                    v___x_5333_ = lean_nat_dec_lt(v___x_5331_, v___x_5332_);
                    if v___x_5333_ == 0 {
                        crate::leanh::lean_dec(v___x_5331_);
                        crate::leanh::lean_del_object(v___x_5319_);
                        crate::leanh::lean_dec(v_a_5317_);
                        crate::leanh::lean_dec_ref(v_opts_4128_);
                        v___x_5334_ =
                            l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26;
                        v___x_5335_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5334_);
                        crate::leanh::lean_dec_ref(v___x_5335_);
                        state = 14;
                        continue;
                    } else {
                        v___x_5336_ = lean_usize_of_nat(v___x_5331_);
                        crate::leanh::lean_dec(v___x_5331_);
                        v___x_5337_ = lean_internal_set_thread_stack_size(v___x_5336_);
                        v_leanOpts_5338_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                        v_forwardedArgs_5339_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                        v_component_5340_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        );
                        v_printPrefix_5341_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        );
                        v_printLibDir_5342_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10)
                                as u32,
                        );
                        v_useStdin_5343_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11)
                                as u32,
                        );
                        v_onlyDeps_5344_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12)
                                as u32,
                        );
                        v_onlySrcDeps_5345_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13)
                                as u32,
                        );
                        v_depsJson_5346_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14)
                                as u32,
                        );
                        v_opts_5347_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                        v_trustLevel_5348_ = crate::leanh::lean_ctor_get_uint32(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        );
                        v_numThreads_5349_ = crate::leanh::lean_ctor_get_uint32(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        );
                        v_rootDir_x3f_5350_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                        v_setupFileName_x3f_5351_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                        v_oleanFileName_x3f_5352_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                        v_ileanFileName_x3f_5353_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                        v_rustFileName_x3f_5354_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                        v_bcFileName_x3f_5355_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                        v_jsonOutput_5356_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15)
                                as u32,
                        );
                        v_errorOnKinds_5357_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                        v_printStats_5358_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16)
                                as u32,
                        );
                        v_run_5359_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17)
                                as u32,
                        );
                        v_isSharedCheck_5372_ =
                            (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                        if v_isSharedCheck_5372_ == 0 {
                            v___x_5361_ = v_opts_4128_;
                            v_isShared_5362_ = v_isSharedCheck_5372_;
                            state = 148;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_errorOnKinds_5357_);
                            crate::leanh::lean_inc(v_bcFileName_x3f_5355_);
                            crate::leanh::lean_inc(v_rustFileName_x3f_5354_);
                            crate::leanh::lean_inc(v_ileanFileName_x3f_5353_);
                            crate::leanh::lean_inc(v_oleanFileName_x3f_5352_);
                            crate::leanh::lean_inc(v_setupFileName_x3f_5351_);
                            crate::leanh::lean_inc(v_rootDir_x3f_5350_);
                            crate::leanh::lean_inc(v_opts_5347_);
                            crate::leanh::lean_inc(v_forwardedArgs_5339_);
                            crate::leanh::lean_inc(v_leanOpts_5338_);
                            crate::leanh::lean_dec(v_opts_4128_);
                            v___x_5361_ = crate::leanh::lean_box(0);
                            v_isShared_5362_ = v_isSharedCheck_5372_;
                            state = 148;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5324_);
                    crate::leanh::lean_del_object(v___x_5319_);
                    crate::leanh::lean_dec(v_a_5317_);
                    crate::leanh::lean_dec_ref(v_opts_4128_);
                    v___x_5373_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28;
                    v___x_5374_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5373_);
                    crate::leanh::lean_dec_ref(v___x_5374_);
                    state = 13;
                    continue;
                }
            }
            148 => {
                v___x_5363_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27;
                v___x_5364_ = lean_string_append(v___x_5363_, v_a_5317_);
                crate::leanh::lean_dec(v_a_5317_);
                v___x_5365_ = lean_array_push(v_forwardedArgs_5339_, v___x_5364_);
                if v_isShared_5362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5361_, 1, v___x_5365_);
                    v___x_5367_ = v___x_5361_;
                    state = 149;
                    continue;
                } else {
                    v_reuseFailAlloc_5371_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_leanOpts_5338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 1, v___x_5365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 2, v_opts_5347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 3, v_rootDir_x3f_5350_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5371_,
                        4,
                        v_setupFileName_x3f_5351_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5371_,
                        5,
                        v_oleanFileName_x3f_5352_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5371_,
                        6,
                        v_ileanFileName_x3f_5353_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5371_,
                        7,
                        v_rustFileName_x3f_5354_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 8, v_bcFileName_x3f_5355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 9, v_errorOnKinds_5357_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5340_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5341_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5342_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5343_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5344_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5345_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5346_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5348_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5349_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5356_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5358_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5359_,
                    );
                    v___x_5367_ = v_reuseFailAlloc_5371_;
                    state = 149;
                    continue;
                }
            }
            149 => {
                if v_isShared_5320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5319_, 0, v___x_5367_);
                    v___x_5369_ = v___x_5319_;
                    state = 150;
                    continue;
                } else {
                    v_reuseFailAlloc_5370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5367_);
                    v___x_5369_ = v_reuseFailAlloc_5370_;
                    state = 150;
                    continue;
                }
            }
            150 => {
                return v___x_5369_;
            }
            151 => {
                v___x_5378_ = lean_io_error_to_string(v_a_5376_);
                v___x_5379_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5378_,
                    );
                crate::leanh::lean_dec_ref(v___x_5379_);
                state = 12;
                continue;
            }
            152 => {
                v_leanOpts_5388_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                v_forwardedArgs_5389_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                v_component_5390_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_5391_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_5392_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_5393_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_5394_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_5395_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_5396_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_opts_5397_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                v_trustLevel_5398_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_numThreads_5399_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                );
                v_rootDir_x3f_5400_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                v_setupFileName_x3f_5401_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                v_oleanFileName_x3f_5402_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                v_ileanFileName_x3f_5403_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                v_rustFileName_x3f_5404_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                v_jsonOutput_5405_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_5406_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                v_printStats_5407_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_5408_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                v_isSharedCheck_5419_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                if v_isSharedCheck_5419_ == 0 {
                    v_unused_5420_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                    crate::leanh::lean_dec(v_unused_5420_);
                    v___x_5410_ = v_opts_4128_;
                    v_isShared_5411_ = v_isSharedCheck_5419_;
                    state = 153;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_errorOnKinds_5406_);
                    crate::leanh::lean_inc(v_rustFileName_x3f_5404_);
                    crate::leanh::lean_inc(v_ileanFileName_x3f_5403_);
                    crate::leanh::lean_inc(v_oleanFileName_x3f_5402_);
                    crate::leanh::lean_inc(v_setupFileName_x3f_5401_);
                    crate::leanh::lean_inc(v_rootDir_x3f_5400_);
                    crate::leanh::lean_inc(v_opts_5397_);
                    crate::leanh::lean_inc(v_forwardedArgs_5389_);
                    crate::leanh::lean_inc(v_leanOpts_5388_);
                    crate::leanh::lean_dec(v_opts_4128_);
                    v___x_5410_ = crate::leanh::lean_box(0);
                    v_isShared_5411_ = v_isSharedCheck_5419_;
                    state = 153;
                    continue;
                }
            }
            153 => {
                v___x_5412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5412_, 0, v_a_5384_);
                if v_isShared_5411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5410_, 8, v___x_5412_);
                    v___x_5414_ = v___x_5410_;
                    state = 154;
                    continue;
                } else {
                    v_reuseFailAlloc_5418_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_leanOpts_5388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 1, v_forwardedArgs_5389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 2, v_opts_5397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 3, v_rootDir_x3f_5400_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5418_,
                        4,
                        v_setupFileName_x3f_5401_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5418_,
                        5,
                        v_oleanFileName_x3f_5402_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5418_,
                        6,
                        v_ileanFileName_x3f_5403_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5418_,
                        7,
                        v_rustFileName_x3f_5404_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 8, v___x_5412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 9, v_errorOnKinds_5406_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5390_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5391_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5392_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5393_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5394_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5395_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5396_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5398_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5399_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5405_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5407_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5408_,
                    );
                    v___x_5414_ = v_reuseFailAlloc_5418_;
                    state = 154;
                    continue;
                }
            }
            154 => {
                if v_isShared_5387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5386_, 0, v___x_5414_);
                    v___x_5416_ = v___x_5386_;
                    state = 155;
                    continue;
                } else {
                    v_reuseFailAlloc_5417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5414_);
                    v___x_5416_ = v_reuseFailAlloc_5417_;
                    state = 155;
                    continue;
                }
            }
            155 => {
                return v___x_5416_;
            }
            156 => {
                v___x_5424_ = lean_io_error_to_string(v_a_5422_);
                v___x_5425_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5424_,
                    );
                crate::leanh::lean_dec_ref(v___x_5425_);
                state = 57;
                continue;
            }
            157 => {
                v_leanOpts_5434_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                v_forwardedArgs_5435_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                v_component_5436_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_5437_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_5438_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_5439_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_5440_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_5441_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_5442_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_opts_5443_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                v_trustLevel_5444_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_numThreads_5445_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                );
                v_rootDir_x3f_5446_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                v_setupFileName_x3f_5447_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                v_oleanFileName_x3f_5448_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                v_ileanFileName_x3f_5449_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                v_bcFileName_x3f_5450_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                v_jsonOutput_5451_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_5452_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                v_printStats_5453_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_5454_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                v_isSharedCheck_5465_ = (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                if v_isSharedCheck_5465_ == 0 {
                    v_unused_5466_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                    crate::leanh::lean_dec(v_unused_5466_);
                    v___x_5456_ = v_opts_4128_;
                    v_isShared_5457_ = v_isSharedCheck_5465_;
                    state = 158;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_errorOnKinds_5452_);
                    crate::leanh::lean_inc(v_bcFileName_x3f_5450_);
                    crate::leanh::lean_inc(v_ileanFileName_x3f_5449_);
                    crate::leanh::lean_inc(v_oleanFileName_x3f_5448_);
                    crate::leanh::lean_inc(v_setupFileName_x3f_5447_);
                    crate::leanh::lean_inc(v_rootDir_x3f_5446_);
                    crate::leanh::lean_inc(v_opts_5443_);
                    crate::leanh::lean_inc(v_forwardedArgs_5435_);
                    crate::leanh::lean_inc(v_leanOpts_5434_);
                    crate::leanh::lean_dec(v_opts_4128_);
                    v___x_5456_ = crate::leanh::lean_box(0);
                    v_isShared_5457_ = v_isSharedCheck_5465_;
                    state = 158;
                    continue;
                }
            }
            158 => {
                v___x_5458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5458_, 0, v_a_5430_);
                if v_isShared_5457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5456_, 7, v___x_5458_);
                    v___x_5460_ = v___x_5456_;
                    state = 159;
                    continue;
                } else {
                    v_reuseFailAlloc_5464_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_leanOpts_5434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5464_, 1, v_forwardedArgs_5435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5464_, 2, v_opts_5443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5464_, 3, v_rootDir_x3f_5446_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5464_,
                        4,
                        v_setupFileName_x3f_5447_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5464_,
                        5,
                        v_oleanFileName_x3f_5448_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5464_,
                        6,
                        v_ileanFileName_x3f_5449_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5464_, 7, v___x_5458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5464_, 8, v_bcFileName_x3f_5450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5464_, 9, v_errorOnKinds_5452_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5436_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5437_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5438_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5439_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5440_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5441_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5442_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5444_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                        v_numThreads_5445_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5451_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5453_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5454_,
                    );
                    v___x_5460_ = v_reuseFailAlloc_5464_;
                    state = 159;
                    continue;
                }
            }
            159 => {
                if v_isShared_5433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5432_, 0, v___x_5460_);
                    v___x_5462_ = v___x_5432_;
                    state = 160;
                    continue;
                } else {
                    v_reuseFailAlloc_5463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5460_);
                    v___x_5462_ = v_reuseFailAlloc_5463_;
                    state = 160;
                    continue;
                }
            }
            160 => {
                return v___x_5462_;
            }
            161 => {
                v___x_5470_ = lean_io_error_to_string(v_a_5468_);
                v___x_5471_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5470_,
                    );
                crate::leanh::lean_dec_ref(v___x_5471_);
                state = 10;
                continue;
            }
            162 => {
                v___x_5479_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_5478_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5477_, 1);
                    crate::leanh::lean_ctor_set(v___x_5477_, 0, v___x_5479_);
                    v___x_5481_ = v___x_5477_;
                    state = 163;
                    continue;
                } else {
                    v_reuseFailAlloc_5482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5482_, 0, v___x_5479_);
                    v___x_5481_ = v_reuseFailAlloc_5482_;
                    state = 163;
                    continue;
                }
            }
            163 => {
                return v___x_5481_;
            }
            164 => {
                v___x_5487_ = lean_io_error_to_string(v_a_5485_);
                v___x_5488_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5487_,
                    );
                crate::leanh::lean_dec_ref(v___x_5488_);
                state = 59;
                continue;
            }
            165 => {
                v___x_5495_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_5494_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5493_, 1);
                    crate::leanh::lean_ctor_set(v___x_5493_, 0, v___x_5495_);
                    v___x_5497_ = v___x_5493_;
                    state = 166;
                    continue;
                } else {
                    v_reuseFailAlloc_5498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5498_, 0, v___x_5495_);
                    v___x_5497_ = v_reuseFailAlloc_5498_;
                    state = 166;
                    continue;
                }
            }
            166 => {
                return v___x_5497_;
            }
            167 => {
                v___x_5503_ = lean_io_error_to_string(v_a_5501_);
                v___x_5504_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5503_,
                    );
                crate::leanh::lean_dec_ref(v___x_5504_);
                state = 8;
                continue;
            }
            168 => {
                v___x_5512_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_5511_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5510_, 1);
                    crate::leanh::lean_ctor_set(v___x_5510_, 0, v___x_5512_);
                    v___x_5514_ = v___x_5510_;
                    state = 169;
                    continue;
                } else {
                    v_reuseFailAlloc_5515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5515_, 0, v___x_5512_);
                    v___x_5514_ = v_reuseFailAlloc_5515_;
                    state = 169;
                    continue;
                }
            }
            169 => {
                return v___x_5514_;
            }
            170 => {
                v___x_5520_ = lean_io_error_to_string(v_a_5518_);
                v___x_5521_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5520_,
                    );
                crate::leanh::lean_dec_ref(v___x_5521_);
                state = 61;
                continue;
            }
            171 => {
                v___x_5529_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_5528_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5527_, 1);
                    crate::leanh::lean_ctor_set(v___x_5527_, 0, v___x_5529_);
                    v___x_5531_ = v___x_5527_;
                    state = 172;
                    continue;
                } else {
                    v_reuseFailAlloc_5532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5532_, 0, v___x_5529_);
                    v___x_5531_ = v_reuseFailAlloc_5532_;
                    state = 172;
                    continue;
                }
            }
            172 => {
                return v___x_5531_;
            }
            173 => {
                v___x_5537_ = lean_io_error_to_string(v_a_5535_);
                v___x_5538_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5537_,
                    );
                crate::leanh::lean_dec_ref(v___x_5538_);
                state = 6;
                continue;
            }
            174 => {
                v___x_5546_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_5545_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5544_, 1);
                    crate::leanh::lean_ctor_set(v___x_5544_, 0, v___x_5546_);
                    v___x_5548_ = v___x_5544_;
                    state = 175;
                    continue;
                } else {
                    v_reuseFailAlloc_5549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5546_);
                    v___x_5548_ = v_reuseFailAlloc_5549_;
                    state = 175;
                    continue;
                }
            }
            175 => {
                return v___x_5548_;
            }
            176 => {
                v___x_5554_ = lean_io_error_to_string(v_a_5552_);
                v___x_5555_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5554_,
                    );
                crate::leanh::lean_dec_ref(v___x_5555_);
                state = 63;
                continue;
            }
            177 => {
                v___x_5564_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5565_ = lean_string_utf8_byte_size(v_a_5560_);
                crate::leanh::lean_inc(v_a_5560_);
                v___x_5566_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5566_, 0, v_a_5560_);
                crate::leanh::lean_ctor_set(v___x_5566_, 1, v___x_5564_);
                crate::leanh::lean_ctor_set(v___x_5566_, 2, v___x_5565_);
                v___x_5567_ = l_String_Slice_toNat_x3f(v___x_5566_);
                crate::leanh::lean_dec_ref_known(v___x_5566_, 3);
                if crate::leanh::lean_obj_tag(v___x_5567_) == 1 {
                    v_val_5568_ = crate::leanh::lean_ctor_get(v___x_5567_, 0);
                    crate::leanh::lean_inc(v_val_5568_);
                    crate::leanh::lean_dec_ref_known(v___x_5567_, 1);
                    v___x_5569_ = crate::leanh::lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
                    v___x_5570_ = lean_nat_dec_lt(v_val_5568_, v___x_5569_);
                    if v___x_5570_ == 0 {
                        crate::leanh::lean_dec(v_val_5568_);
                        crate::leanh::lean_del_object(v___x_5562_);
                        crate::leanh::lean_dec(v_a_5560_);
                        crate::leanh::lean_dec_ref(v_opts_4128_);
                        v___x_5571_ =
                            l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32;
                        v___x_5572_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5571_);
                        crate::leanh::lean_dec_ref(v___x_5572_);
                        state = 4;
                        continue;
                    } else {
                        v_leanOpts_5573_ = crate::leanh::lean_ctor_get(v_opts_4128_, 0);
                        v_forwardedArgs_5574_ = crate::leanh::lean_ctor_get(v_opts_4128_, 1);
                        v_component_5575_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        );
                        v_printPrefix_5576_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        );
                        v_printLibDir_5577_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10)
                                as u32,
                        );
                        v_useStdin_5578_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11)
                                as u32,
                        );
                        v_onlyDeps_5579_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12)
                                as u32,
                        );
                        v_onlySrcDeps_5580_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13)
                                as u32,
                        );
                        v_depsJson_5581_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14)
                                as u32,
                        );
                        v_opts_5582_ = crate::leanh::lean_ctor_get(v_opts_4128_, 2);
                        v_trustLevel_5583_ = crate::leanh::lean_ctor_get_uint32(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        );
                        v_rootDir_x3f_5584_ = crate::leanh::lean_ctor_get(v_opts_4128_, 3);
                        v_setupFileName_x3f_5585_ = crate::leanh::lean_ctor_get(v_opts_4128_, 4);
                        v_oleanFileName_x3f_5586_ = crate::leanh::lean_ctor_get(v_opts_4128_, 5);
                        v_ileanFileName_x3f_5587_ = crate::leanh::lean_ctor_get(v_opts_4128_, 6);
                        v_rustFileName_x3f_5588_ = crate::leanh::lean_ctor_get(v_opts_4128_, 7);
                        v_bcFileName_x3f_5589_ = crate::leanh::lean_ctor_get(v_opts_4128_, 8);
                        v_jsonOutput_5590_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15)
                                as u32,
                        );
                        v_errorOnKinds_5591_ = crate::leanh::lean_ctor_get(v_opts_4128_, 9);
                        v_printStats_5592_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16)
                                as u32,
                        );
                        v_run_5593_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_4128_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17)
                                as u32,
                        );
                        v_isSharedCheck_5607_ =
                            (!crate::leanh::lean_is_exclusive(v_opts_4128_)) as u8;
                        if v_isSharedCheck_5607_ == 0 {
                            v___x_5595_ = v_opts_4128_;
                            v_isShared_5596_ = v_isSharedCheck_5607_;
                            state = 178;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_errorOnKinds_5591_);
                            crate::leanh::lean_inc(v_bcFileName_x3f_5589_);
                            crate::leanh::lean_inc(v_rustFileName_x3f_5588_);
                            crate::leanh::lean_inc(v_ileanFileName_x3f_5587_);
                            crate::leanh::lean_inc(v_oleanFileName_x3f_5586_);
                            crate::leanh::lean_inc(v_setupFileName_x3f_5585_);
                            crate::leanh::lean_inc(v_rootDir_x3f_5584_);
                            crate::leanh::lean_inc(v_opts_5582_);
                            crate::leanh::lean_inc(v_forwardedArgs_5574_);
                            crate::leanh::lean_inc(v_leanOpts_5573_);
                            crate::leanh::lean_dec(v_opts_4128_);
                            v___x_5595_ = crate::leanh::lean_box(0);
                            v_isShared_5596_ = v_isSharedCheck_5607_;
                            state = 178;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5567_);
                    crate::leanh::lean_del_object(v___x_5562_);
                    crate::leanh::lean_dec(v_a_5560_);
                    crate::leanh::lean_dec_ref(v_opts_4128_);
                    v___x_5608_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34;
                    v___x_5609_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_5608_);
                    crate::leanh::lean_dec_ref(v___x_5609_);
                    state = 3;
                    continue;
                }
            }
            178 => {
                v___x_5597_ = lean_uint32_of_nat(v_val_5568_);
                crate::leanh::lean_dec(v_val_5568_);
                v___x_5598_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33;
                v___x_5599_ = lean_string_append(v___x_5598_, v_a_5560_);
                crate::leanh::lean_dec(v_a_5560_);
                v___x_5600_ = lean_array_push(v_forwardedArgs_5574_, v___x_5599_);
                if v_isShared_5596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5595_, 1, v___x_5600_);
                    v___x_5602_ = v___x_5595_;
                    state = 179;
                    continue;
                } else {
                    v_reuseFailAlloc_5606_ = crate::leanh::lean_alloc_ctor(0, 10, (18) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_leanOpts_5573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 1, v___x_5600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 2, v_opts_5582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 3, v_rootDir_x3f_5584_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5606_,
                        4,
                        v_setupFileName_x3f_5585_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5606_,
                        5,
                        v_oleanFileName_x3f_5586_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5606_,
                        6,
                        v_ileanFileName_x3f_5587_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5606_,
                        7,
                        v_rustFileName_x3f_5588_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 8, v_bcFileName_x3f_5589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 9, v_errorOnKinds_5591_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                        v_component_5575_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                        v_printPrefix_5576_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                        v_printLibDir_5577_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                        v_useStdin_5578_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                        v_onlyDeps_5579_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                        v_onlySrcDeps_5580_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                        v_depsJson_5581_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_trustLevel_5583_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                        v_jsonOutput_5590_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                        v_printStats_5592_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                        v_run_5593_,
                    );
                    v___x_5602_ = v_reuseFailAlloc_5606_;
                    state = 179;
                    continue;
                }
            }
            179 => {
                crate::leanh::lean_ctor_set_uint32(
                    v___x_5602_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 4) as u32,
                    v___x_5597_,
                );
                if v_isShared_5563_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5562_, 0, v___x_5602_);
                    v___x_5604_ = v___x_5562_;
                    state = 180;
                    continue;
                } else {
                    v_reuseFailAlloc_5605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
                    v___x_5604_ = v_reuseFailAlloc_5605_;
                    state = 180;
                    continue;
                }
            }
            180 => {
                return v___x_5604_;
            }
            181 => {
                v___x_5613_ = lean_io_error_to_string(v_a_5611_);
                v___x_5614_ =
                    l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(
                        v___x_5613_,
                    );
                crate::leanh::lean_dec_ref(v___x_5614_);
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(
    mut v_opts_5619_: *mut crate::leanh::LeanObject,
    mut v_opt_5620_: *mut crate::leanh::LeanObject,
    mut v_optArg_x3f_5621_: *mut crate::leanh::LeanObject,
    mut v_a_5622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_opt_boxed_5623_: u32 = 0;
    let mut v_res_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_opt_boxed_5623_ = crate::leanh::lean_unbox_uint32(v_opt_5620_);
    crate::leanh::lean_dec(v_opt_5620_);
    v_res_5624_ = lean_shell_options_process(v_opts_5619_, v_opt_boxed_5623_, v_optArg_x3f_5621_);
    return v_res_5624_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(
    mut v_opts_5625_: *mut crate::leanh::LeanObject,
    mut v_opt_5626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5627_ = crate::leanh::lean_ctor_get(v_opt_5626_, 0);
    v_defValue_5628_ = crate::leanh::lean_ctor_get(v_opt_5626_, 1);
    v_map_5629_ = crate::leanh::lean_ctor_get(v_opts_5625_, 0);
    v___x_5630_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5629_,
            v_name_5627_,
        );
    if crate::leanh::lean_obj_tag(v___x_5630_) == 0 {
        crate::leanh::lean_inc(v_defValue_5628_);
        return v_defValue_5628_;
    } else {
        let mut v_val_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5631_ = crate::leanh::lean_ctor_get(v___x_5630_, 0);
        crate::leanh::lean_inc(v_val_5631_);
        crate::leanh::lean_dec_ref_known(v___x_5630_, 1);
        if crate::leanh::lean_obj_tag(v_val_5631_) == 3 {
            let mut v_v_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_5632_ = crate::leanh::lean_ctor_get(v_val_5631_, 0);
            crate::leanh::lean_inc(v_v_5632_);
            crate::leanh::lean_dec_ref_known(v_val_5631_, 1);
            return v_v_5632_;
        } else {
            crate::leanh::lean_dec(v_val_5631_);
            crate::leanh::lean_inc(v_defValue_5628_);
            return v_defValue_5628_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(
    mut v_opts_5633_: *mut crate::leanh::LeanObject,
    mut v_opt_5634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5635_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(
        v_opts_5633_,
        v_opt_5634_,
    );
    crate::leanh::lean_dec_ref(v_opt_5634_);
    crate::leanh::lean_dec_ref(v_opts_5633_);
    return v_res_5635_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5637_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__0;
    v___x_5638_ = lean_string_utf8_byte_size(v___x_5637_);
    return v___x_5638_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg(
    mut v_s_5639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: u8 = 0;
    v___x_5640_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__0;
    v___x_5641_ = lean_string_utf8_byte_size(v_s_5639_);
    v___x_5642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__1_once), _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg___closed__1);
    v___x_5643_ = lean_nat_dec_le(v___x_5642_, v___x_5641_);
    if v___x_5643_ == 0 {
        let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_5639_);
        v___x_5644_ = crate::leanh::lean_box(0);
        return v___x_5644_;
    } else {
        let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5646_: u8 = 0;
        v___x_5645_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5646_ = lean_string_memcmp(
            v_s_5639_,
            v___x_5640_,
            v___x_5645_,
            v___x_5645_,
            v___x_5642_,
        );
        if v___x_5646_ == 0 {
            let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_s_5639_);
            v___x_5647_ = crate::leanh::lean_box(0);
            return v___x_5647_;
        } else {
            let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_s_5639_);
            v___x_5648_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5648_, 0, v_s_5639_);
            crate::leanh::lean_ctor_set(v___x_5648_, 1, v___x_5645_);
            crate::leanh::lean_ctor_set(v___x_5648_, 2, v___x_5641_);
            v___x_5649_ = l_String_Slice_pos_x21(v___x_5648_, v___x_5642_);
            crate::leanh::lean_dec_ref_known(v___x_5648_, 3);
            v___x_5650_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5650_, 0, v_s_5639_);
            crate::leanh::lean_ctor_set(v___x_5650_, 1, v___x_5649_);
            crate::leanh::lean_ctor_set(v___x_5650_, 2, v___x_5641_);
            v___x_5651_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5651_, 0, v___x_5650_);
            return v___x_5651_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(
    mut v_s_5652_: *mut crate::leanh::LeanObject,
    mut v_pat_5653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5654_ =
        l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg(
            v_s_5652_,
        );
    return v___x_5654_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(
    mut v_s_5655_: *mut crate::leanh::LeanObject,
    mut v_pat_5656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5657_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(
        v_s_5655_,
        v_pat_5656_,
    );
    crate::leanh::lean_dec_ref(v_pat_5656_);
    return v_res_5657_;
}
pub unsafe fn l___private_Lean_Shell_0__Lean_shellMain___lam__0(
    mut v___x_5659_: *mut crate::leanh::LeanObject,
    mut v___x_5660_: *mut crate::leanh::LeanObject,
    mut v_mainModuleName_5661_: *mut crate::leanh::LeanObject,
    mut v_a_5662_: *mut crate::leanh::LeanObject,
    mut v___x_5663_: *mut crate::leanh::LeanObject,
    mut v_fileName_5664_: *mut crate::leanh::LeanObject,
    mut v___x_5665_: *mut crate::leanh::LeanObject,
    mut v___x_5666_: *mut crate::leanh::LeanObject,
    mut v___x_5667_: *mut crate::leanh::LeanObject,
    mut v___x_5668_: *mut crate::leanh::LeanObject,
    mut v___x_5669_: *mut crate::leanh::LeanObject,
    mut v___x_5670_: *mut crate::leanh::LeanObject,
    mut v___x_5671_: *mut crate::leanh::LeanObject,
    mut v___x_5672_: *mut crate::leanh::LeanObject,
    mut v_run_5673_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: u8 = 0;
    let mut v_fileName_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5695_: u8 = 0;
    let mut v_inheritedTraceOptions_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5709_: u8 = 0;
    let mut v_msg_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut v___y_5726_: u8 = 0;
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5738_: u8 = 0;
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut v_unused_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5675_ = lean_io_get_num_heartbeats();
                v___x_5676_ = lean_st_mk_ref(v___x_5659_);
                v___x_5677_ = l_Lean_inheritedTraceOptions;
                v___x_5678_ = lean_st_ref_get(v___x_5677_);
                v___x_5679_ = lean_st_ref_get(v___x_5676_);
                v_env_5680_ = crate::leanh::lean_ctor_get(v___x_5679_, 0);
                crate::leanh::lean_inc_ref(v_env_5680_);
                crate::leanh::lean_dec(v___x_5679_);
                v___x_5681_ = l_Lean_diagnostics;
                v___x_5682_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_5660_, v___x_5681_);
                v___x_5746_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5680_);
                crate::leanh::lean_dec_ref(v_env_5680_);
                if v___x_5746_ == 0 {
                    if v___x_5682_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5663_);
                        crate::leanh::lean_inc(v___x_5676_);
                        crate::leanh::lean_inc(v___x_5668_);
                        v_fileName_5684_ = v_fileName_5664_;
                        v_fileMap_5685_ = v___x_5665_;
                        v_currRecDepth_5686_ = v___x_5666_;
                        v_ref_5687_ = v___x_5667_;
                        v_currNamespace_5688_ = v___x_5668_;
                        v_openDecls_5689_ = v___x_5669_;
                        v_initHeartbeats_5690_ = v___x_5675_;
                        v_maxHeartbeats_5691_ = v___x_5670_;
                        v_quotContext_5692_ = v___x_5668_;
                        v_currMacroScope_5693_ = v___x_5671_;
                        v_cancelTk_x3f_5694_ = v___x_5672_;
                        v_suppressElabErrors_5695_ = v_run_5673_;
                        v_inheritedTraceOptions_5696_ = v___x_5678_;
                        v___y_5697_ = v___x_5676_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5726_ = v___x_5746_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_5726_ = v___x_5682_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_5698_ = l_Lean_maxRecDepth;
                v___x_5699_ =
                    l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(
                        v___x_5660_,
                        v___x_5698_,
                    );
                v___x_5700_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_5700_, 0, v_fileName_5684_);
                crate::leanh::lean_ctor_set(v___x_5700_, 1, v_fileMap_5685_);
                crate::leanh::lean_ctor_set(v___x_5700_, 2, v___x_5660_);
                crate::leanh::lean_ctor_set(v___x_5700_, 3, v_currRecDepth_5686_);
                crate::leanh::lean_ctor_set(v___x_5700_, 4, v___x_5699_);
                crate::leanh::lean_ctor_set(v___x_5700_, 5, v_ref_5687_);
                crate::leanh::lean_ctor_set(v___x_5700_, 6, v_currNamespace_5688_);
                crate::leanh::lean_ctor_set(v___x_5700_, 7, v_openDecls_5689_);
                crate::leanh::lean_ctor_set(v___x_5700_, 8, v_initHeartbeats_5690_);
                crate::leanh::lean_ctor_set(v___x_5700_, 9, v_maxHeartbeats_5691_);
                crate::leanh::lean_ctor_set(v___x_5700_, 10, v_quotContext_5692_);
                crate::leanh::lean_ctor_set(v___x_5700_, 11, v_currMacroScope_5693_);
                crate::leanh::lean_ctor_set(v___x_5700_, 12, v_cancelTk_x3f_5694_);
                crate::leanh::lean_ctor_set(v___x_5700_, 13, v_inheritedTraceOptions_5696_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5700_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___x_5682_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5700_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5695_,
                );
                v___x_5701_ =
                    l_Lean_Compiler_LCNF_emitRust(v_mainModuleName_5661_, v___x_5700_, v___y_5697_);
                crate::leanh::lean_dec(v___y_5697_);
                crate::leanh::lean_dec_ref_known(v___x_5700_, 14);
                if crate::leanh::lean_obj_tag(v___x_5701_) == 0 {
                    v_a_5702_ = crate::leanh::lean_ctor_get(v___x_5701_, 0);
                    crate::leanh::lean_inc(v_a_5702_);
                    crate::leanh::lean_dec_ref_known(v___x_5701_, 1);
                    v___x_5703_ = lean_st_ref_get(v___x_5676_);
                    crate::leanh::lean_dec(v___x_5676_);
                    crate::leanh::lean_dec(v___x_5703_);
                    v___x_5704_ = lean_string_to_utf8(v_a_5702_);
                    crate::leanh::lean_dec(v_a_5702_);
                    v___x_5705_ = lean_io_prim_handle_write(v_a_5662_, v___x_5704_);
                    crate::leanh::lean_dec_ref(v___x_5704_);
                    return v___x_5705_;
                } else {
                    crate::leanh::lean_dec(v___x_5676_);
                    v_a_5706_ = crate::leanh::lean_ctor_get(v___x_5701_, 0);
                    v_isSharedCheck_5724_ = (!crate::leanh::lean_is_exclusive(v___x_5701_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5708_ = v___x_5701_;
                        v_isShared_5709_ = v_isSharedCheck_5724_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5706_);
                        crate::leanh::lean_dec(v___x_5701_);
                        v___x_5708_ = crate::leanh::lean_box(0);
                        v_isShared_5709_ = v_isSharedCheck_5724_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5706_) == 0 {
                    v_msg_5710_ = crate::leanh::lean_ctor_get(v_a_5706_, 1);
                    crate::leanh::lean_inc_ref(v_msg_5710_);
                    crate::leanh::lean_dec_ref_known(v_a_5706_, 2);
                    v___x_5711_ = l_Lean_MessageData_toString(v_msg_5710_);
                    v___x_5712_ = lean_mk_io_user_error(v___x_5711_);
                    if v_isShared_5709_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5708_, 0, v___x_5712_);
                        v___x_5714_ = v___x_5708_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5712_);
                        v___x_5714_ = v_reuseFailAlloc_5715_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_id_5716_ = crate::leanh::lean_ctor_get(v_a_5706_, 0);
                    crate::leanh::lean_inc(v_id_5716_);
                    crate::leanh::lean_dec_ref_known(v_a_5706_, 2);
                    v___x_5717_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
                    v___x_5718_ = l_Nat_reprFast(v_id_5716_);
                    v___x_5719_ = lean_string_append(v___x_5717_, v___x_5718_);
                    crate::leanh::lean_dec_ref(v___x_5718_);
                    v___x_5720_ = lean_mk_io_user_error(v___x_5719_);
                    if v_isShared_5709_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5708_, 0, v___x_5720_);
                        v___x_5722_ = v___x_5708_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 0, v___x_5720_);
                        v___x_5722_ = v_reuseFailAlloc_5723_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5714_;
            }
            4 => {
                return v___x_5722_;
            }
            5 => {
                if v___y_5726_ == 0 {
                    v___x_5727_ = lean_st_ref_take(v___x_5676_);
                    v_env_5728_ = crate::leanh::lean_ctor_get(v___x_5727_, 0);
                    v_nextMacroScope_5729_ = crate::leanh::lean_ctor_get(v___x_5727_, 1);
                    v_ngen_5730_ = crate::leanh::lean_ctor_get(v___x_5727_, 2);
                    v_auxDeclNGen_5731_ = crate::leanh::lean_ctor_get(v___x_5727_, 3);
                    v_traceState_5732_ = crate::leanh::lean_ctor_get(v___x_5727_, 4);
                    v_messages_5733_ = crate::leanh::lean_ctor_get(v___x_5727_, 6);
                    v_infoState_5734_ = crate::leanh::lean_ctor_get(v___x_5727_, 7);
                    v_snapshotTasks_5735_ = crate::leanh::lean_ctor_get(v___x_5727_, 8);
                    v_isSharedCheck_5744_ = (!crate::leanh::lean_is_exclusive(v___x_5727_)) as u8;
                    if v_isSharedCheck_5744_ == 0 {
                        v_unused_5745_ = crate::leanh::lean_ctor_get(v___x_5727_, 5);
                        crate::leanh::lean_dec(v_unused_5745_);
                        v___x_5737_ = v___x_5727_;
                        v_isShared_5738_ = v_isSharedCheck_5744_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_5735_);
                        crate::leanh::lean_inc(v_infoState_5734_);
                        crate::leanh::lean_inc(v_messages_5733_);
                        crate::leanh::lean_inc(v_traceState_5732_);
                        crate::leanh::lean_inc(v_auxDeclNGen_5731_);
                        crate::leanh::lean_inc(v_ngen_5730_);
                        crate::leanh::lean_inc(v_nextMacroScope_5729_);
                        crate::leanh::lean_inc(v_env_5728_);
                        crate::leanh::lean_dec(v___x_5727_);
                        v___x_5737_ = crate::leanh::lean_box(0);
                        v_isShared_5738_ = v_isSharedCheck_5744_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5663_);
                    crate::leanh::lean_inc(v___x_5676_);
                    crate::leanh::lean_inc(v___x_5668_);
                    v_fileName_5684_ = v_fileName_5664_;
                    v_fileMap_5685_ = v___x_5665_;
                    v_currRecDepth_5686_ = v___x_5666_;
                    v_ref_5687_ = v___x_5667_;
                    v_currNamespace_5688_ = v___x_5668_;
                    v_openDecls_5689_ = v___x_5669_;
                    v_initHeartbeats_5690_ = v___x_5675_;
                    v_maxHeartbeats_5691_ = v___x_5670_;
                    v_quotContext_5692_ = v___x_5668_;
                    v_currMacroScope_5693_ = v___x_5671_;
                    v_cancelTk_x3f_5694_ = v___x_5672_;
                    v_suppressElabErrors_5695_ = v_run_5673_;
                    v_inheritedTraceOptions_5696_ = v___x_5678_;
                    v___y_5697_ = v___x_5676_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_5739_ = l_Lean_Kernel_enableDiag(v_env_5728_, v___x_5682_);
                if v_isShared_5738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5737_, 5, v___x_5663_);
                    crate::leanh::lean_ctor_set(v___x_5737_, 0, v___x_5739_);
                    v___x_5741_ = v___x_5737_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 0, v___x_5739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 1, v_nextMacroScope_5729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 2, v_ngen_5730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 3, v_auxDeclNGen_5731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 4, v_traceState_5732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 5, v___x_5663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 6, v_messages_5733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 7, v_infoState_5734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 8, v_snapshotTasks_5735_);
                    v___x_5741_ = v_reuseFailAlloc_5743_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5742_ = lean_st_ref_set(v___x_5676_, v___x_5741_);
                crate::leanh::lean_inc(v___x_5676_);
                crate::leanh::lean_inc(v___x_5668_);
                v_fileName_5684_ = v_fileName_5664_;
                v_fileMap_5685_ = v___x_5665_;
                v_currRecDepth_5686_ = v___x_5666_;
                v_ref_5687_ = v___x_5667_;
                v_currNamespace_5688_ = v___x_5668_;
                v_openDecls_5689_ = v___x_5669_;
                v_initHeartbeats_5690_ = v___x_5675_;
                v_maxHeartbeats_5691_ = v___x_5670_;
                v_quotContext_5692_ = v___x_5668_;
                v_currMacroScope_5693_ = v___x_5671_;
                v_cancelTk_x3f_5694_ = v___x_5672_;
                v_suppressElabErrors_5695_ = v_run_5673_;
                v_inheritedTraceOptions_5696_ = v___x_5678_;
                v___y_5697_ = v___x_5676_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(
    mut v___x_5747_: *mut crate::leanh::LeanObject,
    mut v___x_5748_: *mut crate::leanh::LeanObject,
    mut v_mainModuleName_5749_: *mut crate::leanh::LeanObject,
    mut v_a_5750_: *mut crate::leanh::LeanObject,
    mut v___x_5751_: *mut crate::leanh::LeanObject,
    mut v_fileName_5752_: *mut crate::leanh::LeanObject,
    mut v___x_5753_: *mut crate::leanh::LeanObject,
    mut v___x_5754_: *mut crate::leanh::LeanObject,
    mut v___x_5755_: *mut crate::leanh::LeanObject,
    mut v___x_5756_: *mut crate::leanh::LeanObject,
    mut v___x_5757_: *mut crate::leanh::LeanObject,
    mut v___x_5758_: *mut crate::leanh::LeanObject,
    mut v___x_5759_: *mut crate::leanh::LeanObject,
    mut v___x_5760_: *mut crate::leanh::LeanObject,
    mut v_run_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_run_boxed_5763_: u8 = 0;
    let mut v_res_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_run_boxed_5763_ = (crate::leanh::lean_unbox(v_run_5761_) as u8);
    v_res_5764_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(
        v___x_5747_,
        v___x_5748_,
        v_mainModuleName_5749_,
        v_a_5750_,
        v___x_5751_,
        v_fileName_5752_,
        v___x_5753_,
        v___x_5754_,
        v___x_5755_,
        v___x_5756_,
        v___x_5757_,
        v___x_5758_,
        v___x_5759_,
        v___x_5760_,
        v_run_boxed_5763_,
    );
    crate::leanh::lean_dec(v_a_5750_);
    return v_res_5764_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(
    mut v_val_5765_: *mut crate::leanh::LeanObject,
    mut v_a_5766_: *mut crate::leanh::LeanObject,
    mut v_b_5767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: u8 = 0;
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: u32 = 0;
    let mut v___x_5775_: u32 = 0;
    let mut v___x_5776_: u8 = 0;
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_5768_ = crate::leanh::lean_ctor_get(v_val_5765_, 0);
                v_startInclusive_5769_ = crate::leanh::lean_ctor_get(v_val_5765_, 1);
                v_endExclusive_5770_ = crate::leanh::lean_ctor_get(v_val_5765_, 2);
                v___x_5771_ = lean_nat_sub(v_endExclusive_5770_, v_startInclusive_5769_);
                v___x_5772_ = lean_nat_dec_eq(v_a_5766_, v___x_5771_);
                crate::leanh::lean_dec(v___x_5771_);
                if v___x_5772_ == 0 {
                    v___x_5773_ = lean_nat_add(v_startInclusive_5769_, v_a_5766_);
                    v___x_5774_ = lean_string_utf8_get_fast(v_str_5768_, v___x_5773_);
                    v___x_5775_ = 10;
                    v___x_5776_ = lean_uint32_dec_eq(v___x_5774_, v___x_5775_);
                    if v___x_5776_ == 0 {
                        crate::leanh::lean_dec(v_a_5766_);
                        v___x_5777_ = crate::leanh::lean_box(0);
                        v___x_5778_ = lean_string_utf8_next_fast(v_str_5768_, v___x_5773_);
                        crate::leanh::lean_dec(v___x_5773_);
                        v___x_5779_ = lean_nat_sub(v___x_5778_, v_startInclusive_5769_);
                        v_a_5766_ = v___x_5779_;
                        v_b_5767_ = v___x_5777_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5773_);
                        v___x_5781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5781_, 0, v_a_5766_);
                        return v___x_5781_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5766_);
                    crate::leanh::lean_inc(v_b_5767_);
                    return v_b_5767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___boxed(
    mut v_val_5782_: *mut crate::leanh::LeanObject,
    mut v_a_5783_: *mut crate::leanh::LeanObject,
    mut v_b_5784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5785_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_val_5782_, v_a_5783_, v_b_5784_);
    crate::leanh::lean_dec(v_b_5784_);
    crate::leanh::lean_dec_ref(v_val_5782_);
    return v_res_5785_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(
    mut v_s_5786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5788_: u32 = 0;
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5788_ = 10;
    v___x_5789_ = lean_string_push(v_s_5786_, v___x_5788_);
    v___x_5790_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(v___x_5789_);
    return v___x_5790_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(
    mut v_s_5791_: *mut crate::leanh::LeanObject,
    mut v_a_5792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5793_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_s_5791_);
    return v_res_5793_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0() -> u8 {
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: u8 = 0;
    v___x_5794_ = crate::leanh::lean_box(0);
    v___x_5795_ = lean_internal_has_address_sanitizer(v___x_5794_);
    return v___x_5795_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5800_ = l_Lean_Options_empty;
    v___x_5801_ = l_Lean_Core_getMaxHeartbeats(v___x_5800_);
    return v___x_5801_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5803_ = l_Lean_firstFrontendMacroScope;
    v___x_5804_ = lean_nat_add(v___x_5803_, v___x_5802_);
    return v___x_5804_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5815_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5816_ = lean_mk_empty_array_with_capacity(v___x_5815_);
    v___x_5817_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5817_, 0, v___x_5816_);
    return v___x_5817_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5818_: usize = 0;
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5818_ = 5usize;
    v___x_5819_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5820_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5821_ = lean_mk_empty_array_with_capacity(v___x_5820_);
    v___x_5822_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__10),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__10_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10,
    );
    v___x_5823_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5823_, 0, v___x_5822_);
    crate::leanh::lean_ctor_set(v___x_5823_, 1, v___x_5821_);
    crate::leanh::lean_ctor_set(v___x_5823_, 2, v___x_5819_);
    crate::leanh::lean_ctor_set(v___x_5823_, 3, v___x_5819_);
    crate::leanh::lean_ctor_set_usize(v___x_5823_, 4, v___x_5818_);
    return v___x_5823_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: u64 = 0;
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__11),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__11_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11,
    );
    v___x_5825_ = 0u64;
    v___x_5826_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_5826_, 0, v___x_5824_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_5826_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5825_,
    );
    return v___x_5826_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5827_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5827_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__13),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__13_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13,
    );
    v___x_5829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5829_, 0, v___x_5828_);
    return v___x_5829_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__14),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__14_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14,
    );
    v___x_5831_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5831_, 0, v___x_5830_);
    crate::leanh::lean_ctor_set(v___x_5831_, 1, v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5832_ = l_Lean_NameSet_empty;
    v___x_5833_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__11),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__11_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11,
    );
    v___x_5834_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5834_, 0, v___x_5833_);
    crate::leanh::lean_ctor_set(v___x_5834_, 1, v___x_5833_);
    crate::leanh::lean_ctor_set(v___x_5834_, 2, v___x_5832_);
    return v___x_5834_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: u8 = 0;
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__11),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__11_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11,
    );
    v___x_5836_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__14),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__14_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14,
    );
    v___x_5837_ = 1;
    v___x_5838_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5838_, 0, v___x_5836_);
    crate::leanh::lean_ctor_set(v___x_5838_, 1, v___x_5836_);
    crate::leanh::lean_ctor_set(v___x_5838_, 2, v___x_5835_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5838_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5837_,
    );
    return v___x_5838_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5844_ = l___private_Lean_Shell_0__Lean_shellMain___closed__21;
    v___x_5845_ = lean_string_utf8_byte_size(v___x_5844_);
    return v___x_5845_;
}
pub unsafe fn _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5846_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__22),
        core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__22_once),
        _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22,
    );
    v___x_5847_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5848_ = l___private_Lean_Shell_0__Lean_shellMain___closed__21;
    v___x_5849_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5849_, 0, v___x_5848_);
    crate::leanh::lean_ctor_set(v___x_5849_, 1, v___x_5847_);
    crate::leanh::lean_ctor_set(v___x_5849_, 2, v___x_5846_);
    return v___x_5849_;
}
pub unsafe fn lean_shell_main(
    mut v_args_5853_: *mut crate::leanh::LeanObject,
    mut v_opts_5854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: u8 = 0;
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: u8 = 0;
    let mut v___x_5866_: u8 = 0;
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5875_: u8 = 0;
    let mut v_unused_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fns_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5882_: u8 = 0;
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5887_: u8 = 0;
    let mut v_unused_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5892_: u8 = 0;
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v_leanOpts_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forwardedArgs_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_component_5899_: u8 = 0;
    let mut v_printPrefix_5900_: u8 = 0;
    let mut v_printLibDir_5901_: u8 = 0;
    let mut v_useStdin_5902_: u8 = 0;
    let mut v_onlyDeps_5903_: u8 = 0;
    let mut v_onlySrcDeps_5904_: u8 = 0;
    let mut v_depsJson_5905_: u8 = 0;
    let mut v_trustLevel_5906_: u32 = 0;
    let mut v_rootDir_x3f_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setupFileName_x3f_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanFileName_x3f_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ileanFileName_x3f_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rustFileName_x3f_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bcFileName_x3f_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jsonOutput_5913_: u8 = 0;
    let mut v_errorOnKinds_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_printStats_5915_: u8 = 0;
    let mut v_run_5916_: u8 = 0;
    let mut v___y_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5930_: u8 = 0;
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut v_a_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5938_: u8 = 0;
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5942_: u8 = 0;
    let mut v___x_5943_: u8 = 0;
    let mut v___y_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModuleName_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5957_: u8 = 0;
    let mut v_val_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5986_: u8 = 0;
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5998_: u8 = 0;
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6003_: u8 = 0;
    let mut v_unused_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6008_: u8 = 0;
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6012_: u8 = 0;
    let mut v_val_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u32 = 0;
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6020_: u8 = 0;
    let mut v_a_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6024_: u8 = 0;
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6028_: u8 = 0;
    let mut v___y_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut v___y_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_isSharedCheck_6074_: u8 = 0;
    let mut v___y_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6097_: u8 = 0;
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6102_: u8 = 0;
    let mut v_unused_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6107_: u8 = 0;
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6111_: u8 = 0;
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6137_: u8 = 0;
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6142_: u8 = 0;
    let mut v_unused_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6147_: u8 = 0;
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6151_: u8 = 0;
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6156_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6161_: u8 = 0;
    let mut v_unused_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6166_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut v_a_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6174_: u8 = 0;
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6178_: u8 = 0;
    let mut v___y_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6195_: u8 = 0;
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6200_: u8 = 0;
    let mut v_unused_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6205_: u8 = 0;
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_a_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6213_: u8 = 0;
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6217_: u8 = 0;
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: u8 = 0;
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6228_: u8 = 0;
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6233_: u8 = 0;
    let mut v_unused_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6238_: u8 = 0;
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6242_: u8 = 0;
    let mut v_a_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6246_: u8 = 0;
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6250_: u8 = 0;
    let mut v___y_6252_: u8 = 0;
    let mut v_fst_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6256_: u8 = 0;
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6269_: u8 = 0;
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6273_: u8 = 0;
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timeout_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: u8 = 0;
    let mut v___x_6282_: usize = 0;
    let mut v___x_6283_: usize = 0;
    let mut v___x_6284_: usize = 0;
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxMemory_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: u8 = 0;
    let mut v___x_6290_: usize = 0;
    let mut v___x_6291_: usize = 0;
    let mut v___x_6292_: usize = 0;
    let mut v___x_6293_: usize = 0;
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6302_: u8 = 0;
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6307_: u8 = 0;
    let mut v_unused_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6312_: u8 = 0;
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6316_: u8 = 0;
    let mut v_a_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6320_: u8 = 0;
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6324_: u8 = 0;
    let mut v_a_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6328_: u8 = 0;
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6332_: u8 = 0;
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6338_: u8 = 0;
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6343_: u8 = 0;
    let mut v_unused_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6348_: u8 = 0;
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6352_: u8 = 0;
    let mut v_a_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6356_: u8 = 0;
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_leanOpts_5897_ = crate::leanh::lean_ctor_get(v_opts_5854_, 0);
                crate::leanh::lean_inc_ref(v_leanOpts_5897_);
                v_forwardedArgs_5898_ = crate::leanh::lean_ctor_get(v_opts_5854_, 1);
                crate::leanh::lean_inc_ref(v_forwardedArgs_5898_);
                v_component_5899_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 8) as u32,
                );
                v_printPrefix_5900_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 9) as u32,
                );
                v_printLibDir_5901_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 10) as u32,
                );
                v_useStdin_5902_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 11) as u32,
                );
                v_onlyDeps_5903_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 12) as u32,
                );
                v_onlySrcDeps_5904_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 13) as u32,
                );
                v_depsJson_5905_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 14) as u32,
                );
                v_trustLevel_5906_ = crate::leanh::lean_ctor_get_uint32(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_rootDir_x3f_5907_ = crate::leanh::lean_ctor_get(v_opts_5854_, 3);
                crate::leanh::lean_inc(v_rootDir_x3f_5907_);
                v_setupFileName_x3f_5908_ = crate::leanh::lean_ctor_get(v_opts_5854_, 4);
                crate::leanh::lean_inc(v_setupFileName_x3f_5908_);
                v_oleanFileName_x3f_5909_ = crate::leanh::lean_ctor_get(v_opts_5854_, 5);
                crate::leanh::lean_inc(v_oleanFileName_x3f_5909_);
                v_ileanFileName_x3f_5910_ = crate::leanh::lean_ctor_get(v_opts_5854_, 6);
                crate::leanh::lean_inc(v_ileanFileName_x3f_5910_);
                v_rustFileName_x3f_5911_ = crate::leanh::lean_ctor_get(v_opts_5854_, 7);
                crate::leanh::lean_inc(v_rustFileName_x3f_5911_);
                v_bcFileName_x3f_5912_ = crate::leanh::lean_ctor_get(v_opts_5854_, 8);
                crate::leanh::lean_inc(v_bcFileName_x3f_5912_);
                v_jsonOutput_5913_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 15) as u32,
                );
                v_errorOnKinds_5914_ = crate::leanh::lean_ctor_get(v_opts_5854_, 9);
                crate::leanh::lean_inc_ref(v_errorOnKinds_5914_);
                v_printStats_5915_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 16) as u32,
                );
                v_run_5916_ = crate::leanh::lean_ctor_get_uint8(
                    v_opts_5854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 17) as u32,
                );
                crate::leanh::lean_dec_ref(v_opts_5854_);
                if v_printPrefix_5900_ == 0 {
                    if v_printLibDir_5901_ == 0 {
                        v___x_5943_ = 1;
                        v___x_6286_ = l___private_Lean_Shell_0__Lean_maxMemory;
                        v_maxMemory_6287_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_5897_, v___x_6286_);
                        v___x_6288_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6289_ = lean_nat_dec_eq(v_maxMemory_6287_, v___x_6288_);
                        if v___x_6289_ == 0 {
                            v___x_6290_ = lean_usize_of_nat(v_maxMemory_6287_);
                            crate::leanh::lean_dec(v_maxMemory_6287_);
                            v___x_6291_ = 1024usize;
                            v___x_6292_ = lean_usize_mul(v___x_6290_, v___x_6291_);
                            v___x_6293_ = lean_usize_mul(v___x_6292_, v___x_6291_);
                            v___x_6294_ = lean_internal_set_max_memory(v___x_6293_);
                            state = 71;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_maxMemory_6287_);
                            state = 71;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                        crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                        crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                        crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                        crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                        crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                        crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                        crate::leanh::lean_dec_ref(v_forwardedArgs_5898_);
                        crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                        crate::leanh::lean_dec(v_args_5853_);
                        v___x_6295_ = l_Lean_getBuildDir();
                        if crate::leanh::lean_obj_tag(v___x_6295_) == 0 {
                            v_a_6296_ = crate::leanh::lean_ctor_get(v___x_6295_, 0);
                            crate::leanh::lean_inc(v_a_6296_);
                            crate::leanh::lean_dec_ref_known(v___x_6295_, 1);
                            v___x_6297_ = l_Lean_getLibDir(v_a_6296_);
                            if crate::leanh::lean_obj_tag(v___x_6297_) == 0 {
                                v_a_6298_ = crate::leanh::lean_ctor_get(v___x_6297_, 0);
                                crate::leanh::lean_inc(v_a_6298_);
                                crate::leanh::lean_dec_ref_known(v___x_6297_, 1);
                                v___x_6299_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_a_6298_);
                                if crate::leanh::lean_obj_tag(v___x_6299_) == 0 {
                                    v_isSharedCheck_6307_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6299_)) as u8;
                                    if v_isSharedCheck_6307_ == 0 {
                                        v_unused_6308_ =
                                            crate::leanh::lean_ctor_get(v___x_6299_, 0);
                                        crate::leanh::lean_dec(v_unused_6308_);
                                        v___x_6301_ = v___x_6299_;
                                        v_isShared_6302_ = v_isSharedCheck_6307_;
                                        state = 72;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_6299_);
                                        v___x_6301_ = crate::leanh::lean_box(0);
                                        v_isShared_6302_ = v_isSharedCheck_6307_;
                                        state = 72;
                                        continue;
                                    }
                                } else {
                                    v_a_6309_ = crate::leanh::lean_ctor_get(v___x_6299_, 0);
                                    v_isSharedCheck_6316_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6299_)) as u8;
                                    if v_isSharedCheck_6316_ == 0 {
                                        v___x_6311_ = v___x_6299_;
                                        v_isShared_6312_ = v_isSharedCheck_6316_;
                                        state = 74;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6309_);
                                        crate::leanh::lean_dec(v___x_6299_);
                                        v___x_6311_ = crate::leanh::lean_box(0);
                                        v_isShared_6312_ = v_isSharedCheck_6316_;
                                        state = 74;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_6317_ = crate::leanh::lean_ctor_get(v___x_6297_, 0);
                                v_isSharedCheck_6324_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6297_)) as u8;
                                if v_isSharedCheck_6324_ == 0 {
                                    v___x_6319_ = v___x_6297_;
                                    v_isShared_6320_ = v_isSharedCheck_6324_;
                                    state = 76;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6317_);
                                    crate::leanh::lean_dec(v___x_6297_);
                                    v___x_6319_ = crate::leanh::lean_box(0);
                                    v_isShared_6320_ = v_isSharedCheck_6324_;
                                    state = 76;
                                    continue;
                                }
                            }
                        } else {
                            v_a_6325_ = crate::leanh::lean_ctor_get(v___x_6295_, 0);
                            v_isSharedCheck_6332_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6295_)) as u8;
                            if v_isSharedCheck_6332_ == 0 {
                                v___x_6327_ = v___x_6295_;
                                v_isShared_6328_ = v_isSharedCheck_6332_;
                                state = 78;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6325_);
                                crate::leanh::lean_dec(v___x_6295_);
                                v___x_6327_ = crate::leanh::lean_box(0);
                                v_isShared_6328_ = v_isSharedCheck_6332_;
                                state = 78;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                    crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                    crate::leanh::lean_dec_ref(v_forwardedArgs_5898_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    crate::leanh::lean_dec(v_args_5853_);
                    v___x_6333_ = l_Lean_getBuildDir();
                    if crate::leanh::lean_obj_tag(v___x_6333_) == 0 {
                        v_a_6334_ = crate::leanh::lean_ctor_get(v___x_6333_, 0);
                        crate::leanh::lean_inc(v_a_6334_);
                        crate::leanh::lean_dec_ref_known(v___x_6333_, 1);
                        v___x_6335_ =
                            l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(
                                v_a_6334_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_6335_) == 0 {
                            v_isSharedCheck_6343_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6335_)) as u8;
                            if v_isSharedCheck_6343_ == 0 {
                                v_unused_6344_ = crate::leanh::lean_ctor_get(v___x_6335_, 0);
                                crate::leanh::lean_dec(v_unused_6344_);
                                v___x_6337_ = v___x_6335_;
                                v_isShared_6338_ = v_isSharedCheck_6343_;
                                state = 80;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6335_);
                                v___x_6337_ = crate::leanh::lean_box(0);
                                v_isShared_6338_ = v_isSharedCheck_6343_;
                                state = 80;
                                continue;
                            }
                        } else {
                            v_a_6345_ = crate::leanh::lean_ctor_get(v___x_6335_, 0);
                            v_isSharedCheck_6352_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6335_)) as u8;
                            if v_isSharedCheck_6352_ == 0 {
                                v___x_6347_ = v___x_6335_;
                                v_isShared_6348_ = v_isSharedCheck_6352_;
                                state = 82;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6345_);
                                crate::leanh::lean_dec(v___x_6335_);
                                v___x_6347_ = crate::leanh::lean_box(0);
                                v_isShared_6348_ = v_isSharedCheck_6352_;
                                state = 82;
                                continue;
                            }
                        }
                    } else {
                        v_a_6353_ = crate::leanh::lean_ctor_get(v___x_6333_, 0);
                        v_isSharedCheck_6360_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6333_)) as u8;
                        if v_isSharedCheck_6360_ == 0 {
                            v___x_6355_ = v___x_6333_;
                            v_isShared_6356_ = v_isSharedCheck_6360_;
                            state = 84;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6353_);
                            crate::leanh::lean_dec(v___x_6333_);
                            v___x_6355_ = crate::leanh::lean_box(0);
                            v_isShared_6356_ = v_isSharedCheck_6360_;
                            state = 84;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5857_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                v___x_5858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5858_, 0, v___x_5857_);
                return v___x_5858_;
            }
            2 => {
                v___x_5860_ = 0;
                v___x_5861_ = lean_io_exit(v___x_5860_);
                return v___x_5861_;
            }
            3 => {
                v___x_5864_ = lean_display_cumulative_profiling_times();
                v___x_5865_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__0),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_shellMain___closed__0_once
                    ),
                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0,
                );
                if v___x_5865_ == 0 {
                    if crate::leanh::lean_obj_tag(v___y_5863_) == 0 {
                        if v___x_5865_ == 0 {
                            v___x_5866_ = 1;
                            v___x_5867_ = lean_io_exit(v___x_5866_);
                            return v___x_5867_;
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_5863_, 1);
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___y_5863_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_5875_ =
                            (!crate::leanh::lean_is_exclusive(v___y_5863_)) as u8;
                        if v_isSharedCheck_5875_ == 0 {
                            v_unused_5876_ = crate::leanh::lean_ctor_get(v___y_5863_, 0);
                            crate::leanh::lean_dec(v_unused_5876_);
                            v___x_5869_ = v___y_5863_;
                            v_isShared_5870_ = v_isSharedCheck_5875_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_5863_);
                            v___x_5869_ = crate::leanh::lean_box(0);
                            v_isShared_5870_ = v_isSharedCheck_5875_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v___x_5865_ == 0 {
                    crate::leanh::lean_del_object(v___x_5869_);
                    state = 1;
                    continue;
                } else {
                    v___x_5871_ =
                        l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                    if v_isShared_5870_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5869_, 0);
                        crate::leanh::lean_ctor_set(v___x_5869_, 0, v___x_5871_);
                        v___x_5873_ = v___x_5869_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5874_, 0, v___x_5871_);
                        v___x_5873_ = v_reuseFailAlloc_5874_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5873_;
            }
            6 => {
                v___x_5879_ = l_Lean_printImportsJson(v_fns_5878_);
                if crate::leanh::lean_obj_tag(v___x_5879_) == 0 {
                    v_isSharedCheck_5887_ = (!crate::leanh::lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5887_ == 0 {
                        v_unused_5888_ = crate::leanh::lean_ctor_get(v___x_5879_, 0);
                        crate::leanh::lean_dec(v_unused_5888_);
                        v___x_5881_ = v___x_5879_;
                        v_isShared_5882_ = v_isSharedCheck_5887_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5879_);
                        v___x_5881_ = crate::leanh::lean_box(0);
                        v_isShared_5882_ = v_isSharedCheck_5887_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_5889_ = crate::leanh::lean_ctor_get(v___x_5879_, 0);
                    v_isSharedCheck_5896_ = (!crate::leanh::lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5896_ == 0 {
                        v___x_5891_ = v___x_5879_;
                        v_isShared_5892_ = v_isSharedCheck_5896_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5889_);
                        crate::leanh::lean_dec(v___x_5879_);
                        v___x_5891_ = crate::leanh::lean_box(0);
                        v_isShared_5892_ = v_isSharedCheck_5896_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_5883_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_5882_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5881_, 0, v___x_5883_);
                    v___x_5885_ = v___x_5881_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5886_, 0, v___x_5883_);
                    v___x_5885_ = v_reuseFailAlloc_5886_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5885_;
            }
            9 => {
                if v_isShared_5892_ == 0 {
                    v___x_5894_ = v___x_5891_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_a_5889_);
                    v___x_5894_ = v_reuseFailAlloc_5895_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5894_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_bcFileName_x3f_5912_) == 1 {
                    v_val_5921_ = crate::leanh::lean_ctor_get(v_bcFileName_x3f_5912_, 0);
                    crate::leanh::lean_inc(v_val_5921_);
                    crate::leanh::lean_dec_ref_known(v_bcFileName_x3f_5912_, 1);
                    v___x_5922_ = lean_init_llvm();
                    if crate::leanh::lean_obj_tag(v___x_5922_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5922_, 1);
                        v___x_5923_ = l___private_Lean_Shell_0__Lean_shellMain___closed__1;
                        v___x_5924_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_Shell_0__Lean_emitLLVM___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___x_5924_, 0, v___y_5920_);
                        crate::leanh::lean_closure_set(v___x_5924_, 1, v___y_5919_);
                        crate::leanh::lean_closure_set(v___x_5924_, 2, v_val_5921_);
                        v___x_5925_ = crate::leanh::lean_box(0);
                        v___x_5926_ = l_Lean_profileitIOUnsafe___redArg(
                            v___x_5923_,
                            v_leanOpts_5897_,
                            v___x_5924_,
                            v___x_5925_,
                        );
                        crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                        if crate::leanh::lean_obj_tag(v___x_5926_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5926_, 1);
                            v___y_5863_ = v___y_5918_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_5918_);
                            v_a_5927_ = crate::leanh::lean_ctor_get(v___x_5926_, 0);
                            v_isSharedCheck_5934_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5926_)) as u8;
                            if v_isSharedCheck_5934_ == 0 {
                                v___x_5929_ = v___x_5926_;
                                v_isShared_5930_ = v_isSharedCheck_5934_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5927_);
                                crate::leanh::lean_dec(v___x_5926_);
                                v___x_5929_ = crate::leanh::lean_box(0);
                                v_isShared_5930_ = v_isSharedCheck_5934_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5921_);
                        crate::leanh::lean_dec_ref(v___y_5920_);
                        crate::leanh::lean_dec(v___y_5919_);
                        crate::leanh::lean_dec(v___y_5918_);
                        crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                        v_a_5935_ = crate::leanh::lean_ctor_get(v___x_5922_, 0);
                        v_isSharedCheck_5942_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5922_)) as u8;
                        if v_isSharedCheck_5942_ == 0 {
                            v___x_5937_ = v___x_5922_;
                            v_isShared_5938_ = v_isSharedCheck_5942_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5935_);
                            crate::leanh::lean_dec(v___x_5922_);
                            v___x_5937_ = crate::leanh::lean_box(0);
                            v_isShared_5938_ = v_isSharedCheck_5942_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5920_);
                    crate::leanh::lean_dec(v___y_5919_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v___y_5863_ = v___y_5918_;
                    state = 3;
                    continue;
                }
            }
            12 => {
                if v_isShared_5930_ == 0 {
                    v___x_5932_ = v___x_5929_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_a_5927_);
                    v___x_5932_ = v_reuseFailAlloc_5933_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5932_;
            }
            14 => {
                if v_isShared_5938_ == 0 {
                    v___x_5940_ = v___x_5937_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_a_5935_);
                    v___x_5940_ = v_reuseFailAlloc_5941_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5940_;
            }
            16 => {
                v___x_5951_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5952_ = l___private_Lean_Shell_0__Lean_shellMain___closed__2;
                crate::leanh::lean_inc(v_mainModuleName_5950_);
                crate::leanh::lean_inc_ref(v_leanOpts_5897_);
                v___x_5953_ = l_Lean_Elab_runFrontend(
                    v___y_5947_,
                    v_leanOpts_5897_,
                    v___y_5946_,
                    v_mainModuleName_5950_,
                    v_trustLevel_5906_,
                    v_oleanFileName_x3f_5909_,
                    v_ileanFileName_x3f_5910_,
                    v_jsonOutput_5913_,
                    v_errorOnKinds_5914_,
                    v___x_5952_,
                    v_printStats_5915_,
                    v___y_5948_,
                );
                crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                if crate::leanh::lean_obj_tag(v___x_5953_) == 0 {
                    v_a_5954_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_6020_ = (!crate::leanh::lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_6020_ == 0 {
                        v___x_5956_ = v___x_5953_;
                        v_isShared_5957_ = v_isSharedCheck_6020_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5954_);
                        crate::leanh::lean_dec(v___x_5953_);
                        v___x_5956_ = crate::leanh::lean_box(0);
                        v_isShared_5957_ = v_isSharedCheck_6020_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mainModuleName_5950_);
                    crate::leanh::lean_dec(v___y_5949_);
                    crate::leanh::lean_dec_ref(v___y_5945_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v_a_6021_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_6028_ = (!crate::leanh::lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_6028_ == 0 {
                        v___x_6023_ = v___x_5953_;
                        v_isShared_6024_ = v_isSharedCheck_6028_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6021_);
                        crate::leanh::lean_dec(v___x_5953_);
                        v___x_6023_ = crate::leanh::lean_box(0);
                        v_isShared_6024_ = v_isSharedCheck_6028_;
                        state = 25;
                        continue;
                    }
                }
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_a_5954_) == 1 {
                    if v_run_5916_ == 0 {
                        crate::leanh::lean_del_object(v___x_5956_);
                        crate::leanh::lean_dec(v___y_5949_);
                        if crate::leanh::lean_obj_tag(v_rustFileName_x3f_5911_) == 1 {
                            v_val_5958_ = crate::leanh::lean_ctor_get(v_a_5954_, 0);
                            crate::leanh::lean_inc(v_val_5958_);
                            v_val_5959_ = crate::leanh::lean_ctor_get(v_rustFileName_x3f_5911_, 0);
                            crate::leanh::lean_inc(v_val_5959_);
                            crate::leanh::lean_dec_ref_known(v_rustFileName_x3f_5911_, 1);
                            v___x_5960_ = 1;
                            v___x_5961_ = lean_io_prim_handle_mk(v_val_5959_, v___x_5960_);
                            if crate::leanh::lean_obj_tag(v___x_5961_) == 0 {
                                crate::leanh::lean_dec(v_val_5959_);
                                v_a_5962_ = crate::leanh::lean_ctor_get(v___x_5961_, 0);
                                crate::leanh::lean_inc(v_a_5962_);
                                crate::leanh::lean_dec_ref_known(v___x_5961_, 1);
                                v___x_5963_ = l___private_Lean_Shell_0__Lean_shellMain___closed__3;
                                v___x_5964_ = l_Lean_instInhabitedFileMap_default;
                                v___x_5965_ = l_Lean_Options_empty;
                                v___x_5966_ = crate::leanh::lean_box(0);
                                v___x_5967_ = crate::leanh::lean_box(0);
                                v___x_5968_ = crate::leanh::lean_box(0);
                                v___x_5969_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__4_once
                                    ),
                                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4,
                                );
                                v___x_5970_ = l_Lean_firstFrontendMacroScope;
                                v___x_5971_ = crate::leanh::lean_box(0);
                                v___x_5972_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__5
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__5_once
                                    ),
                                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5,
                                );
                                v___x_5973_ = l___private_Lean_Shell_0__Lean_shellMain___closed__8;
                                v___x_5974_ = l___private_Lean_Shell_0__Lean_shellMain___closed__9;
                                v___x_5975_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__12
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__12_once
                                    ),
                                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12,
                                );
                                v___x_5976_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__15
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__15_once
                                    ),
                                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15,
                                );
                                v___x_5977_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__16
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__16_once
                                    ),
                                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16,
                                );
                                v___x_5978_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__17
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__17_once
                                    ),
                                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17,
                                );
                                crate::leanh::lean_inc(v_val_5958_);
                                v___x_5979_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5979_, 0, v_val_5958_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 1, v___x_5972_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 2, v___x_5973_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 3, v___x_5974_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 4, v___x_5975_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 5, v___x_5976_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 6, v___x_5977_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 7, v___x_5978_);
                                crate::leanh::lean_ctor_set(v___x_5979_, 8, v___x_5952_);
                                v___x_5980_ = crate::leanh::lean_box((v_run_5916_) as usize);
                                crate::leanh::lean_inc(v_mainModuleName_5950_);
                                v___f_5981_ = crate::leanh::lean_alloc_closure(
                                    l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    16,
                                    15,
                                );
                                crate::leanh::lean_closure_set(v___f_5981_, 0, v___x_5979_);
                                crate::leanh::lean_closure_set(v___f_5981_, 1, v___x_5965_);
                                crate::leanh::lean_closure_set(
                                    v___f_5981_,
                                    2,
                                    v_mainModuleName_5950_,
                                );
                                crate::leanh::lean_closure_set(v___f_5981_, 3, v_a_5962_);
                                crate::leanh::lean_closure_set(v___f_5981_, 4, v___x_5976_);
                                crate::leanh::lean_closure_set(v___f_5981_, 5, v___y_5945_);
                                crate::leanh::lean_closure_set(v___f_5981_, 6, v___x_5964_);
                                crate::leanh::lean_closure_set(v___f_5981_, 7, v___x_5951_);
                                crate::leanh::lean_closure_set(v___f_5981_, 8, v___x_5966_);
                                crate::leanh::lean_closure_set(v___f_5981_, 9, v___x_5967_);
                                crate::leanh::lean_closure_set(v___f_5981_, 10, v___x_5968_);
                                crate::leanh::lean_closure_set(v___f_5981_, 11, v___x_5969_);
                                crate::leanh::lean_closure_set(v___f_5981_, 12, v___x_5970_);
                                crate::leanh::lean_closure_set(v___f_5981_, 13, v___x_5971_);
                                crate::leanh::lean_closure_set(v___f_5981_, 14, v___x_5980_);
                                v___x_5982_ = l_Lean_profileitIOUnsafe___redArg(
                                    v___x_5963_,
                                    v_leanOpts_5897_,
                                    v___f_5981_,
                                    v___x_5967_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5982_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5982_, 1);
                                    v___y_5918_ = v_a_5954_;
                                    v___y_5919_ = v_mainModuleName_5950_;
                                    v___y_5920_ = v_val_5958_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_val_5958_);
                                    crate::leanh::lean_dec_ref_known(v_a_5954_, 1);
                                    crate::leanh::lean_dec(v_mainModuleName_5950_);
                                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                                    v_a_5983_ = crate::leanh::lean_ctor_get(v___x_5982_, 0);
                                    v_isSharedCheck_5990_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5982_)) as u8;
                                    if v_isSharedCheck_5990_ == 0 {
                                        v___x_5985_ = v___x_5982_;
                                        v_isShared_5986_ = v_isSharedCheck_5990_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5983_);
                                        crate::leanh::lean_dec(v___x_5982_);
                                        v___x_5985_ = crate::leanh::lean_box(0);
                                        v_isShared_5986_ = v_isSharedCheck_5990_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_5961_, 1);
                                crate::leanh::lean_dec(v_val_5958_);
                                crate::leanh::lean_dec_ref_known(v_a_5954_, 1);
                                crate::leanh::lean_dec(v_mainModuleName_5950_);
                                crate::leanh::lean_dec_ref(v___y_5945_);
                                crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                                crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                                v___x_5991_ = l___private_Lean_Shell_0__Lean_shellMain___closed__18;
                                v___x_5992_ = lean_string_append(v___x_5991_, v_val_5959_);
                                crate::leanh::lean_dec(v_val_5959_);
                                v___x_5993_ =
                                    l___private_Lean_Shell_0__Lean_checkOptArg___closed__1;
                                v___x_5994_ = lean_string_append(v___x_5992_, v___x_5993_);
                                v___x_5995_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v___x_5994_);
                                if crate::leanh::lean_obj_tag(v___x_5995_) == 0 {
                                    v_isSharedCheck_6003_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5995_)) as u8;
                                    if v_isSharedCheck_6003_ == 0 {
                                        v_unused_6004_ =
                                            crate::leanh::lean_ctor_get(v___x_5995_, 0);
                                        crate::leanh::lean_dec(v_unused_6004_);
                                        v___x_5997_ = v___x_5995_;
                                        v_isShared_5998_ = v_isSharedCheck_6003_;
                                        state = 20;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_5995_);
                                        v___x_5997_ = crate::leanh::lean_box(0);
                                        v_isShared_5998_ = v_isSharedCheck_6003_;
                                        state = 20;
                                        continue;
                                    }
                                } else {
                                    v_a_6005_ = crate::leanh::lean_ctor_get(v___x_5995_, 0);
                                    v_isSharedCheck_6012_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5995_)) as u8;
                                    if v_isSharedCheck_6012_ == 0 {
                                        v___x_6007_ = v___x_5995_;
                                        v_isShared_6008_ = v_isSharedCheck_6012_;
                                        state = 22;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6005_);
                                        crate::leanh::lean_dec(v___x_5995_);
                                        v___x_6007_ = crate::leanh::lean_box(0);
                                        v_isShared_6008_ = v_isSharedCheck_6012_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_5945_);
                            crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                            v_val_6013_ = crate::leanh::lean_ctor_get(v_a_5954_, 0);
                            crate::leanh::lean_inc(v_val_6013_);
                            v___y_5918_ = v_a_5954_;
                            v___y_5919_ = v_mainModuleName_5950_;
                            v___y_5920_ = v_val_6013_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mainModuleName_5950_);
                        crate::leanh::lean_dec_ref(v___y_5945_);
                        crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                        crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                        v_val_6014_ = crate::leanh::lean_ctor_get(v_a_5954_, 0);
                        crate::leanh::lean_inc(v_val_6014_);
                        crate::leanh::lean_dec_ref_known(v_a_5954_, 1);
                        v___x_6015_ = lean_eval_main(v_val_6014_, v_leanOpts_5897_, v___y_5949_);
                        crate::leanh::lean_dec(v___y_5949_);
                        crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                        crate::leanh::lean_dec(v_val_6014_);
                        v___x_6016_ = crate::leanh::lean_box_uint32(v___x_6015_);
                        if v_isShared_5957_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5956_, 0, v___x_6016_);
                            v___x_6018_ = v___x_5956_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_6019_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6019_, 0, v___x_6016_);
                            v___x_6018_ = v_reuseFailAlloc_6019_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5956_);
                    crate::leanh::lean_dec(v_mainModuleName_5950_);
                    crate::leanh::lean_dec(v___y_5949_);
                    crate::leanh::lean_dec_ref(v___y_5945_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v___y_5863_ = v_a_5954_;
                    state = 3;
                    continue;
                }
            }
            18 => {
                if v_isShared_5986_ == 0 {
                    v___x_5988_ = v___x_5985_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
                    v___x_5988_ = v_reuseFailAlloc_5989_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5988_;
            }
            20 => {
                v___x_5999_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                if v_isShared_5998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5997_, 0, v___x_5999_);
                    v___x_6001_ = v___x_5997_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6002_, 0, v___x_5999_);
                    v___x_6001_ = v_reuseFailAlloc_6002_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6001_;
            }
            22 => {
                if v_isShared_6008_ == 0 {
                    v___x_6010_ = v___x_6007_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_a_6005_);
                    v___x_6010_ = v_reuseFailAlloc_6011_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6010_;
            }
            24 => {
                return v___x_6018_;
            }
            25 => {
                if v_isShared_6024_ == 0 {
                    v___x_6026_ = v___x_6023_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6027_, 0, v_a_6021_);
                    v___x_6026_ = v_reuseFailAlloc_6027_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6026_;
            }
            27 => {
                if crate::leanh::lean_obj_tag(v___y_6035_) == 0 {
                    v_a_6036_ = crate::leanh::lean_ctor_get(v___y_6035_, 0);
                    crate::leanh::lean_inc(v_a_6036_);
                    crate::leanh::lean_dec_ref_known(v___y_6035_, 1);
                    v___y_5945_ = v___y_6030_;
                    v___y_5946_ = v___y_6031_;
                    v___y_5947_ = v___y_6032_;
                    v___y_5948_ = v___y_6033_;
                    v___y_5949_ = v___y_6034_;
                    v_mainModuleName_5950_ = v_a_6036_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6034_);
                    crate::leanh::lean_dec(v___y_6033_);
                    crate::leanh::lean_dec_ref(v___y_6032_);
                    crate::leanh::lean_dec_ref(v___y_6031_);
                    crate::leanh::lean_dec_ref(v___y_6030_);
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v_a_6037_ = crate::leanh::lean_ctor_get(v___y_6035_, 0);
                    v_isSharedCheck_6044_ = (!crate::leanh::lean_is_exclusive(v___y_6035_)) as u8;
                    if v_isSharedCheck_6044_ == 0 {
                        v___x_6039_ = v___y_6035_;
                        v_isShared_6040_ = v_isSharedCheck_6044_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6037_);
                        crate::leanh::lean_dec(v___y_6035_);
                        v___x_6039_ = crate::leanh::lean_box(0);
                        v_isShared_6040_ = v_isSharedCheck_6044_;
                        state = 28;
                        continue;
                    }
                }
            }
            28 => {
                if v_isShared_6040_ == 0 {
                    v___x_6042_ = v___x_6039_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
                    v___x_6042_ = v_reuseFailAlloc_6043_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6042_;
            }
            30 => {
                if crate::leanh::lean_obj_tag(v_setupFileName_x3f_5908_) == 0 {
                    v___x_6051_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v___y_6048_) == 1 {
                        v_val_6052_ = crate::leanh::lean_ctor_get(v___y_6048_, 0);
                        crate::leanh::lean_inc(v_val_6052_);
                        crate::leanh::lean_dec_ref_known(v___y_6048_, 1);
                        v___x_6053_ = l_Lean_moduleNameOfFileName(v_val_6052_, v_rootDir_x3f_5907_);
                        if crate::leanh::lean_obj_tag(v___x_6053_) == 0 {
                            v___y_6030_ = v___y_6046_;
                            v___y_6031_ = v___y_6047_;
                            v___y_6032_ = v_contents_6050_;
                            v___y_6033_ = v___x_6051_;
                            v___y_6034_ = v___y_6049_;
                            v___y_6035_ = v___x_6053_;
                            state = 27;
                            continue;
                        } else {
                            if crate::leanh::lean_obj_tag(v_oleanFileName_x3f_5909_) == 0 {
                                if crate::leanh::lean_obj_tag(v_rustFileName_x3f_5911_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6053_, 1);
                                    v___x_6054_ =
                                        l___private_Lean_Shell_0__Lean_shellMain___closed__20;
                                    v___y_5945_ = v___y_6046_;
                                    v___y_5946_ = v___y_6047_;
                                    v___y_5947_ = v_contents_6050_;
                                    v___y_5948_ = v___x_6051_;
                                    v___y_5949_ = v___y_6049_;
                                    v_mainModuleName_5950_ = v___x_6054_;
                                    state = 16;
                                    continue;
                                } else {
                                    v___y_6030_ = v___y_6046_;
                                    v___y_6031_ = v___y_6047_;
                                    v___y_6032_ = v_contents_6050_;
                                    v___y_6033_ = v___x_6051_;
                                    v___y_6034_ = v___y_6049_;
                                    v___y_6035_ = v___x_6053_;
                                    state = 27;
                                    continue;
                                }
                            } else {
                                v___y_6030_ = v___y_6046_;
                                v___y_6031_ = v___y_6047_;
                                v___y_6032_ = v_contents_6050_;
                                v___y_6033_ = v___x_6051_;
                                v___y_6034_ = v___y_6049_;
                                v___y_6035_ = v___x_6053_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_6048_);
                        crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                        v___x_6055_ = l___private_Lean_Shell_0__Lean_shellMain___closed__20;
                        v___y_5945_ = v___y_6046_;
                        v___y_5946_ = v___y_6047_;
                        v___y_5947_ = v_contents_6050_;
                        v___y_5948_ = v___x_6051_;
                        v___y_5949_ = v___y_6049_;
                        v_mainModuleName_5950_ = v___x_6055_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6048_);
                    crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                    v_val_6056_ = crate::leanh::lean_ctor_get(v_setupFileName_x3f_5908_, 0);
                    v_isSharedCheck_6074_ =
                        (!crate::leanh::lean_is_exclusive(v_setupFileName_x3f_5908_)) as u8;
                    if v_isSharedCheck_6074_ == 0 {
                        v___x_6058_ = v_setupFileName_x3f_5908_;
                        v_isShared_6059_ = v_isSharedCheck_6074_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6056_);
                        crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                        v___x_6058_ = crate::leanh::lean_box(0);
                        v_isShared_6059_ = v_isSharedCheck_6074_;
                        state = 31;
                        continue;
                    }
                }
            }
            31 => {
                v___x_6060_ = l_Lean_ModuleSetup_load(v_val_6056_);
                crate::leanh::lean_dec(v_val_6056_);
                if crate::leanh::lean_obj_tag(v___x_6060_) == 0 {
                    v_a_6061_ = crate::leanh::lean_ctor_get(v___x_6060_, 0);
                    crate::leanh::lean_inc(v_a_6061_);
                    crate::leanh::lean_dec_ref_known(v___x_6060_, 1);
                    v_name_6062_ = crate::leanh::lean_ctor_get(v_a_6061_, 0);
                    crate::leanh::lean_inc(v_name_6062_);
                    if v_isShared_6059_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6058_, 0, v_a_6061_);
                        v___x_6064_ = v___x_6058_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_6065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6061_);
                        v___x_6064_ = v_reuseFailAlloc_6065_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6058_);
                    crate::leanh::lean_dec_ref(v_contents_6050_);
                    crate::leanh::lean_dec(v___y_6049_);
                    crate::leanh::lean_dec_ref(v___y_6047_);
                    crate::leanh::lean_dec_ref(v___y_6046_);
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v_a_6066_ = crate::leanh::lean_ctor_get(v___x_6060_, 0);
                    v_isSharedCheck_6073_ = (!crate::leanh::lean_is_exclusive(v___x_6060_)) as u8;
                    if v_isSharedCheck_6073_ == 0 {
                        v___x_6068_ = v___x_6060_;
                        v_isShared_6069_ = v_isSharedCheck_6073_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6066_);
                        crate::leanh::lean_dec(v___x_6060_);
                        v___x_6068_ = crate::leanh::lean_box(0);
                        v_isShared_6069_ = v_isSharedCheck_6073_;
                        state = 33;
                        continue;
                    }
                }
            }
            32 => {
                v___y_5945_ = v___y_6046_;
                v___y_5946_ = v___y_6047_;
                v___y_5947_ = v_contents_6050_;
                v___y_5948_ = v___x_6064_;
                v___y_5949_ = v___y_6049_;
                v_mainModuleName_5950_ = v_name_6062_;
                state = 16;
                continue;
            }
            33 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6071_;
            }
            35 => {
                v___x_6084_ = lean_nat_add(v_startInclusive_6078_, v___y_6083_);
                crate::leanh::lean_dec(v___y_6083_);
                crate::leanh::lean_inc(v___x_6084_);
                crate::leanh::lean_inc_ref(v_str_6077_);
                v___x_6085_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6085_, 0, v_str_6077_);
                crate::leanh::lean_ctor_set(v___x_6085_, 1, v_startInclusive_6078_);
                crate::leanh::lean_ctor_set(v___x_6085_, 2, v___x_6084_);
                v___x_6086_ = l_String_Slice_trimAscii(v___x_6085_);
                v___x_6087_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l___private_Lean_Shell_0__Lean_shellMain___closed__23),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Shell_0__Lean_shellMain___closed__23_once
                    ),
                    _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23,
                );
                v___x_6088_ = l_String_Slice_beq(v___x_6086_, v___x_6087_);
                if v___x_6088_ == 0 {
                    crate::leanh::lean_dec(v___x_6084_);
                    crate::leanh::lean_dec(v___y_6082_);
                    crate::leanh::lean_dec(v___y_6081_);
                    crate::leanh::lean_dec_ref(v___y_6080_);
                    crate::leanh::lean_dec(v_endExclusive_6079_);
                    crate::leanh::lean_dec_ref(v_str_6077_);
                    crate::leanh::lean_dec_ref(v___y_6076_);
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                    crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v___x_6089_ = l___private_Lean_Shell_0__Lean_shellMain___closed__24;
                    v___x_6090_ = l_String_Slice_toString(v___x_6086_);
                    crate::leanh::lean_dec_ref(v___x_6086_);
                    v___x_6091_ = lean_string_append(v___x_6089_, v___x_6090_);
                    crate::leanh::lean_dec_ref(v___x_6090_);
                    v___x_6092_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1;
                    v___x_6093_ = lean_string_append(v___x_6091_, v___x_6092_);
                    v___x_6094_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v___x_6093_);
                    if crate::leanh::lean_obj_tag(v___x_6094_) == 0 {
                        v_isSharedCheck_6102_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6094_)) as u8;
                        if v_isSharedCheck_6102_ == 0 {
                            v_unused_6103_ = crate::leanh::lean_ctor_get(v___x_6094_, 0);
                            crate::leanh::lean_dec(v_unused_6103_);
                            v___x_6096_ = v___x_6094_;
                            v_isShared_6097_ = v_isSharedCheck_6102_;
                            state = 36;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6094_);
                            v___x_6096_ = crate::leanh::lean_box(0);
                            v_isShared_6097_ = v_isSharedCheck_6102_;
                            state = 36;
                            continue;
                        }
                    } else {
                        v_a_6104_ = crate::leanh::lean_ctor_get(v___x_6094_, 0);
                        v_isSharedCheck_6111_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6094_)) as u8;
                        if v_isSharedCheck_6111_ == 0 {
                            v___x_6106_ = v___x_6094_;
                            v_isShared_6107_ = v_isSharedCheck_6111_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6104_);
                            crate::leanh::lean_dec(v___x_6094_);
                            v___x_6106_ = crate::leanh::lean_box(0);
                            v_isShared_6107_ = v_isSharedCheck_6111_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_6086_);
                    v___x_6112_ =
                        lean_string_utf8_extract(v_str_6077_, v___x_6084_, v_endExclusive_6079_);
                    crate::leanh::lean_dec(v_endExclusive_6079_);
                    crate::leanh::lean_dec(v___x_6084_);
                    crate::leanh::lean_dec_ref(v_str_6077_);
                    v___y_6046_ = v___y_6076_;
                    v___y_6047_ = v___y_6080_;
                    v___y_6048_ = v___y_6081_;
                    v___y_6049_ = v___y_6082_;
                    v_contents_6050_ = v___x_6112_;
                    state = 30;
                    continue;
                }
            }
            36 => {
                v___x_6098_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                if v_isShared_6097_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6096_, 0, v___x_6098_);
                    v___x_6100_ = v___x_6096_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6098_);
                    v___x_6100_ = v_reuseFailAlloc_6101_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6100_;
            }
            38 => {
                if v_isShared_6107_ == 0 {
                    v___x_6109_ = v___x_6106_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
                    v___x_6109_ = v_reuseFailAlloc_6110_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_6109_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v___y_6117_) == 0 {
                    v_a_6118_ = crate::leanh::lean_ctor_get(v___y_6117_, 0);
                    crate::leanh::lean_inc(v_a_6118_);
                    crate::leanh::lean_dec_ref_known(v___y_6117_, 1);
                    v___x_6119_ = lean_decode_lossy_utf8(v_a_6118_);
                    crate::leanh::lean_dec(v_a_6118_);
                    if v_onlyDeps_5903_ == 0 {
                        if v_onlySrcDeps_5904_ == 0 {
                            crate::leanh::lean_inc_ref(v___x_6119_);
                            v___x_6120_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___redArg(v___x_6119_);
                            if crate::leanh::lean_obj_tag(v___x_6120_) == 1 {
                                crate::leanh::lean_dec_ref(v___x_6119_);
                                v_val_6121_ = crate::leanh::lean_ctor_get(v___x_6120_, 0);
                                crate::leanh::lean_inc(v_val_6121_);
                                crate::leanh::lean_dec_ref_known(v___x_6120_, 1);
                                v___x_6122_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_6123_ = crate::leanh::lean_box(0);
                                v___x_6124_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_val_6121_, v___x_6122_, v___x_6123_);
                                if crate::leanh::lean_obj_tag(v___x_6124_) == 0 {
                                    v_str_6125_ = crate::leanh::lean_ctor_get(v_val_6121_, 0);
                                    crate::leanh::lean_inc_ref(v_str_6125_);
                                    v_startInclusive_6126_ =
                                        crate::leanh::lean_ctor_get(v_val_6121_, 1);
                                    crate::leanh::lean_inc(v_startInclusive_6126_);
                                    v_endExclusive_6127_ =
                                        crate::leanh::lean_ctor_get(v_val_6121_, 2);
                                    crate::leanh::lean_inc(v_endExclusive_6127_);
                                    crate::leanh::lean_dec(v_val_6121_);
                                    v___x_6128_ =
                                        lean_nat_sub(v_endExclusive_6127_, v_startInclusive_6126_);
                                    crate::leanh::lean_inc_ref(v___y_6115_);
                                    v___y_6076_ = v___y_6115_;
                                    v_str_6077_ = v_str_6125_;
                                    v_startInclusive_6078_ = v_startInclusive_6126_;
                                    v_endExclusive_6079_ = v_endExclusive_6127_;
                                    v___y_6080_ = v___y_6115_;
                                    v___y_6081_ = v___y_6114_;
                                    v___y_6082_ = v___y_6116_;
                                    v___y_6083_ = v___x_6128_;
                                    state = 35;
                                    continue;
                                } else {
                                    v_val_6129_ = crate::leanh::lean_ctor_get(v___x_6124_, 0);
                                    crate::leanh::lean_inc(v_val_6129_);
                                    crate::leanh::lean_dec_ref_known(v___x_6124_, 1);
                                    v_str_6130_ = crate::leanh::lean_ctor_get(v_val_6121_, 0);
                                    crate::leanh::lean_inc_ref(v_str_6130_);
                                    v_startInclusive_6131_ =
                                        crate::leanh::lean_ctor_get(v_val_6121_, 1);
                                    crate::leanh::lean_inc(v_startInclusive_6131_);
                                    v_endExclusive_6132_ =
                                        crate::leanh::lean_ctor_get(v_val_6121_, 2);
                                    crate::leanh::lean_inc(v_endExclusive_6132_);
                                    crate::leanh::lean_dec(v_val_6121_);
                                    crate::leanh::lean_inc_ref(v___y_6115_);
                                    v___y_6076_ = v___y_6115_;
                                    v_str_6077_ = v_str_6130_;
                                    v_startInclusive_6078_ = v_startInclusive_6131_;
                                    v_endExclusive_6079_ = v_endExclusive_6132_;
                                    v___y_6080_ = v___y_6115_;
                                    v___y_6081_ = v___y_6114_;
                                    v___y_6082_ = v___y_6116_;
                                    v___y_6083_ = v_val_6129_;
                                    state = 35;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_6120_);
                                crate::leanh::lean_inc_ref(v___y_6115_);
                                v___y_6046_ = v___y_6115_;
                                v___y_6047_ = v___y_6115_;
                                v___y_6048_ = v___y_6114_;
                                v___y_6049_ = v___y_6116_;
                                v_contents_6050_ = v___x_6119_;
                                state = 30;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_6116_);
                            crate::leanh::lean_dec(v___y_6114_);
                            crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                            crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                            crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                            crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                            crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                            crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                            crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                            crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                            v___x_6133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6133_, 0, v___y_6115_);
                            v___x_6134_ = l_Lean_Elab_printImportSrcs(v___x_6119_, v___x_6133_);
                            if crate::leanh::lean_obj_tag(v___x_6134_) == 0 {
                                v_isSharedCheck_6142_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6134_)) as u8;
                                if v_isSharedCheck_6142_ == 0 {
                                    v_unused_6143_ = crate::leanh::lean_ctor_get(v___x_6134_, 0);
                                    crate::leanh::lean_dec(v_unused_6143_);
                                    v___x_6136_ = v___x_6134_;
                                    v_isShared_6137_ = v_isSharedCheck_6142_;
                                    state = 41;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_6134_);
                                    v___x_6136_ = crate::leanh::lean_box(0);
                                    v_isShared_6137_ = v_isSharedCheck_6142_;
                                    state = 41;
                                    continue;
                                }
                            } else {
                                v_a_6144_ = crate::leanh::lean_ctor_get(v___x_6134_, 0);
                                v_isSharedCheck_6151_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6134_)) as u8;
                                if v_isSharedCheck_6151_ == 0 {
                                    v___x_6146_ = v___x_6134_;
                                    v_isShared_6147_ = v_isSharedCheck_6151_;
                                    state = 43;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6144_);
                                    crate::leanh::lean_dec(v___x_6134_);
                                    v___x_6146_ = crate::leanh::lean_box(0);
                                    v_isShared_6147_ = v_isSharedCheck_6151_;
                                    state = 43;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_6116_);
                        crate::leanh::lean_dec(v___y_6114_);
                        crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                        crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                        crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                        crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                        crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                        crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                        crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                        crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                        v___x_6152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6152_, 0, v___y_6115_);
                        v___x_6153_ = l_Lean_Elab_printImports(v___x_6119_, v___x_6152_);
                        if crate::leanh::lean_obj_tag(v___x_6153_) == 0 {
                            v_isSharedCheck_6161_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6153_)) as u8;
                            if v_isSharedCheck_6161_ == 0 {
                                v_unused_6162_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
                                crate::leanh::lean_dec(v_unused_6162_);
                                v___x_6155_ = v___x_6153_;
                                v_isShared_6156_ = v_isSharedCheck_6161_;
                                state = 45;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6153_);
                                v___x_6155_ = crate::leanh::lean_box(0);
                                v_isShared_6156_ = v_isSharedCheck_6161_;
                                state = 45;
                                continue;
                            }
                        } else {
                            v_a_6163_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
                            v_isSharedCheck_6170_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6153_)) as u8;
                            if v_isSharedCheck_6170_ == 0 {
                                v___x_6165_ = v___x_6153_;
                                v_isShared_6166_ = v_isSharedCheck_6170_;
                                state = 47;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6163_);
                                crate::leanh::lean_dec(v___x_6153_);
                                v___x_6165_ = crate::leanh::lean_box(0);
                                v_isShared_6166_ = v_isSharedCheck_6170_;
                                state = 47;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6116_);
                    crate::leanh::lean_dec_ref(v___y_6115_);
                    crate::leanh::lean_dec(v___y_6114_);
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                    crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v_a_6171_ = crate::leanh::lean_ctor_get(v___y_6117_, 0);
                    v_isSharedCheck_6178_ = (!crate::leanh::lean_is_exclusive(v___y_6117_)) as u8;
                    if v_isSharedCheck_6178_ == 0 {
                        v___x_6173_ = v___y_6117_;
                        v_isShared_6174_ = v_isSharedCheck_6178_;
                        state = 49;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6171_);
                        crate::leanh::lean_dec(v___y_6117_);
                        v___x_6173_ = crate::leanh::lean_box(0);
                        v_isShared_6174_ = v_isSharedCheck_6178_;
                        state = 49;
                        continue;
                    }
                }
            }
            41 => {
                v___x_6138_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_6137_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6136_, 0, v___x_6138_);
                    v___x_6140_ = v___x_6136_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_6141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6141_, 0, v___x_6138_);
                    v___x_6140_ = v_reuseFailAlloc_6141_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_6140_;
            }
            43 => {
                if v_isShared_6147_ == 0 {
                    v___x_6149_ = v___x_6146_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6150_, 0, v_a_6144_);
                    v___x_6149_ = v_reuseFailAlloc_6150_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_6149_;
            }
            45 => {
                v___x_6157_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_6156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6155_, 0, v___x_6157_);
                    v___x_6159_ = v___x_6155_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6160_, 0, v___x_6157_);
                    v___x_6159_ = v_reuseFailAlloc_6160_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_6159_;
            }
            47 => {
                if v_isShared_6166_ == 0 {
                    v___x_6168_ = v___x_6165_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_6169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_a_6163_);
                    v___x_6168_ = v_reuseFailAlloc_6169_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_6168_;
            }
            49 => {
                if v_isShared_6174_ == 0 {
                    v___x_6176_ = v___x_6173_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_6177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_a_6171_);
                    v___x_6176_ = v_reuseFailAlloc_6177_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_6176_;
            }
            51 => {
                if v_useStdin_5902_ == 0 {
                    v___x_6183_ = l_IO_FS_readBinFile(v_fileName_6182_);
                    v___y_6114_ = v___y_6180_;
                    v___y_6115_ = v_fileName_6182_;
                    v___y_6116_ = v___y_6181_;
                    v___y_6117_ = v___x_6183_;
                    state = 40;
                    continue;
                } else {
                    v___x_6184_ = lean_get_stdin();
                    v___x_6185_ = l_IO_FS_Stream_readBinToEnd(v___x_6184_);
                    v___y_6114_ = v___y_6180_;
                    v___y_6115_ = v_fileName_6182_;
                    v___y_6116_ = v___y_6181_;
                    v___y_6117_ = v___x_6185_;
                    state = 40;
                    continue;
                }
            }
            52 => {
                if crate::leanh::lean_obj_tag(v___y_6187_) == 1 {
                    v_val_6189_ = crate::leanh::lean_ctor_get(v___y_6187_, 0);
                    crate::leanh::lean_inc(v_val_6189_);
                    v___y_6180_ = v___y_6187_;
                    v___y_6181_ = v___y_6188_;
                    v_fileName_6182_ = v_val_6189_;
                    state = 51;
                    continue;
                } else {
                    if v_useStdin_5902_ == 0 {
                        crate::leanh::lean_dec(v___y_6188_);
                        crate::leanh::lean_dec(v___y_6187_);
                        crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                        crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                        crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                        crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                        crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                        crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                        crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                        crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                        v___x_6190_ = l___private_Lean_Shell_0__Lean_shellMain___closed__25;
                        v___x_6191_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v___x_6190_);
                        if crate::leanh::lean_obj_tag(v___x_6191_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6191_, 1);
                            v___x_6192_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_5943_);
                            if crate::leanh::lean_obj_tag(v___x_6192_) == 0 {
                                v_isSharedCheck_6200_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6192_)) as u8;
                                if v_isSharedCheck_6200_ == 0 {
                                    v_unused_6201_ = crate::leanh::lean_ctor_get(v___x_6192_, 0);
                                    crate::leanh::lean_dec(v_unused_6201_);
                                    v___x_6194_ = v___x_6192_;
                                    v_isShared_6195_ = v_isSharedCheck_6200_;
                                    state = 53;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_6192_);
                                    v___x_6194_ = crate::leanh::lean_box(0);
                                    v_isShared_6195_ = v_isSharedCheck_6200_;
                                    state = 53;
                                    continue;
                                }
                            } else {
                                v_a_6202_ = crate::leanh::lean_ctor_get(v___x_6192_, 0);
                                v_isSharedCheck_6209_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6192_)) as u8;
                                if v_isSharedCheck_6209_ == 0 {
                                    v___x_6204_ = v___x_6192_;
                                    v_isShared_6205_ = v_isSharedCheck_6209_;
                                    state = 55;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6202_);
                                    crate::leanh::lean_dec(v___x_6192_);
                                    v___x_6204_ = crate::leanh::lean_box(0);
                                    v_isShared_6205_ = v_isSharedCheck_6209_;
                                    state = 55;
                                    continue;
                                }
                            }
                        } else {
                            v_a_6210_ = crate::leanh::lean_ctor_get(v___x_6191_, 0);
                            v_isSharedCheck_6217_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6191_)) as u8;
                            if v_isSharedCheck_6217_ == 0 {
                                v___x_6212_ = v___x_6191_;
                                v_isShared_6213_ = v_isSharedCheck_6217_;
                                state = 57;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6210_);
                                crate::leanh::lean_dec(v___x_6191_);
                                v___x_6212_ = crate::leanh::lean_box(0);
                                v_isShared_6213_ = v_isSharedCheck_6217_;
                                state = 57;
                                continue;
                            }
                        }
                    } else {
                        v___x_6218_ = l___private_Lean_Shell_0__Lean_shellMain___closed__26;
                        v___y_6180_ = v___y_6187_;
                        v___y_6181_ = v___y_6188_;
                        v_fileName_6182_ = v___x_6218_;
                        state = 51;
                        continue;
                    }
                }
            }
            53 => {
                v___x_6196_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                if v_isShared_6195_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6194_, 0, v___x_6196_);
                    v___x_6198_ = v___x_6194_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_6199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6199_, 0, v___x_6196_);
                    v___x_6198_ = v_reuseFailAlloc_6199_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_6198_;
            }
            55 => {
                if v_isShared_6205_ == 0 {
                    v___x_6207_ = v___x_6204_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_6208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_a_6202_);
                    v___x_6207_ = v_reuseFailAlloc_6208_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_6207_;
            }
            57 => {
                if v_isShared_6213_ == 0 {
                    v___x_6215_ = v___x_6212_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_6216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
                    v___x_6215_ = v_reuseFailAlloc_6216_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_6215_;
            }
            59 => {
                v___x_6222_ = l_List_isEmpty___redArg(v___y_6221_);
                if v___x_6222_ == 0 {
                    crate::leanh::lean_dec(v___y_6221_);
                    crate::leanh::lean_dec(v___y_6220_);
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                    crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    v___x_6223_ = l___private_Lean_Shell_0__Lean_shellMain___closed__25;
                    v___x_6224_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v___x_6223_);
                    if crate::leanh::lean_obj_tag(v___x_6224_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6224_, 1);
                        v___x_6225_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_5943_);
                        if crate::leanh::lean_obj_tag(v___x_6225_) == 0 {
                            v_isSharedCheck_6233_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6225_)) as u8;
                            if v_isSharedCheck_6233_ == 0 {
                                v_unused_6234_ = crate::leanh::lean_ctor_get(v___x_6225_, 0);
                                crate::leanh::lean_dec(v_unused_6234_);
                                v___x_6227_ = v___x_6225_;
                                v_isShared_6228_ = v_isSharedCheck_6233_;
                                state = 60;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6225_);
                                v___x_6227_ = crate::leanh::lean_box(0);
                                v_isShared_6228_ = v_isSharedCheck_6233_;
                                state = 60;
                                continue;
                            }
                        } else {
                            v_a_6235_ = crate::leanh::lean_ctor_get(v___x_6225_, 0);
                            v_isSharedCheck_6242_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6225_)) as u8;
                            if v_isSharedCheck_6242_ == 0 {
                                v___x_6237_ = v___x_6225_;
                                v_isShared_6238_ = v_isSharedCheck_6242_;
                                state = 62;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6235_);
                                crate::leanh::lean_dec(v___x_6225_);
                                v___x_6237_ = crate::leanh::lean_box(0);
                                v_isShared_6238_ = v_isSharedCheck_6242_;
                                state = 62;
                                continue;
                            }
                        }
                    } else {
                        v_a_6243_ = crate::leanh::lean_ctor_get(v___x_6224_, 0);
                        v_isSharedCheck_6250_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6224_)) as u8;
                        if v_isSharedCheck_6250_ == 0 {
                            v___x_6245_ = v___x_6224_;
                            v_isShared_6246_ = v_isSharedCheck_6250_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6243_);
                            crate::leanh::lean_dec(v___x_6224_);
                            v___x_6245_ = crate::leanh::lean_box(0);
                            v_isShared_6246_ = v_isSharedCheck_6250_;
                            state = 64;
                            continue;
                        }
                    }
                } else {
                    v___y_6187_ = v___y_6220_;
                    v___y_6188_ = v___y_6221_;
                    state = 52;
                    continue;
                }
            }
            60 => {
                v___x_6229_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
                if v_isShared_6228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6227_, 0, v___x_6229_);
                    v___x_6231_ = v___x_6227_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_6232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6232_, 0, v___x_6229_);
                    v___x_6231_ = v_reuseFailAlloc_6232_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_6231_;
            }
            62 => {
                if v_isShared_6238_ == 0 {
                    v___x_6240_ = v___x_6237_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_6241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6241_, 0, v_a_6235_);
                    v___x_6240_ = v_reuseFailAlloc_6241_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_6240_;
            }
            64 => {
                if v_isShared_6246_ == 0 {
                    v___x_6248_ = v___x_6245_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_6249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6249_, 0, v_a_6243_);
                    v___x_6248_ = v_reuseFailAlloc_6249_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_6248_;
            }
            66 => {
                if v_run_5916_ == 0 {
                    v___y_6220_ = v_fst_6253_;
                    v___y_6221_ = v_snd_6254_;
                    state = 59;
                    continue;
                } else {
                    if v___y_6252_ == 0 {
                        v___y_6187_ = v_fst_6253_;
                        v___y_6188_ = v_snd_6254_;
                        state = 52;
                        continue;
                    } else {
                        v___y_6220_ = v_fst_6253_;
                        v___y_6221_ = v_snd_6254_;
                        state = 59;
                        continue;
                    }
                }
            }
            67 => {
                if crate::leanh::lean_obj_tag(v_args_5853_) == 0 {
                    v___x_6257_ = crate::leanh::lean_box(0);
                    v___y_6252_ = v___y_6256_;
                    v_fst_6253_ = v___x_6257_;
                    v_snd_6254_ = v_args_5853_;
                    state = 66;
                    continue;
                } else {
                    v_head_6258_ = crate::leanh::lean_ctor_get(v_args_5853_, 0);
                    crate::leanh::lean_inc(v_head_6258_);
                    v_tail_6259_ = crate::leanh::lean_ctor_get(v_args_5853_, 1);
                    crate::leanh::lean_inc(v_tail_6259_);
                    crate::leanh::lean_dec_ref_known(v_args_5853_, 2);
                    v___x_6260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6260_, 0, v_head_6258_);
                    v___y_6252_ = v___y_6256_;
                    v_fst_6253_ = v___x_6260_;
                    v_snd_6254_ = v_tail_6259_;
                    state = 66;
                    continue;
                }
            }
            68 => match v_component_5899_ {
                0 => {
                    crate::leanh::lean_dec_ref(v_forwardedArgs_5898_);
                    if v_onlyDeps_5903_ == 0 {
                        v___y_6256_ = v_onlyDeps_5903_;
                        state = 67;
                        continue;
                    } else {
                        if v_depsJson_5905_ == 0 {
                            v___y_6256_ = v_depsJson_5905_;
                            state = 67;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                            crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                            crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                            crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                            crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                            crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                            crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                            crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                            if v_useStdin_5902_ == 0 {
                                v___x_6262_ = lean_array_mk(v_args_5853_);
                                v_fns_5878_ = v___x_6262_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_args_5853_);
                                v___x_6263_ = lean_get_stdin();
                                v___x_6264_ = l_IO_FS_Stream_lines(v___x_6263_);
                                if crate::leanh::lean_obj_tag(v___x_6264_) == 0 {
                                    v_a_6265_ = crate::leanh::lean_ctor_get(v___x_6264_, 0);
                                    crate::leanh::lean_inc(v_a_6265_);
                                    crate::leanh::lean_dec_ref_known(v___x_6264_, 1);
                                    v_fns_5878_ = v_a_6265_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_a_6266_ = crate::leanh::lean_ctor_get(v___x_6264_, 0);
                                    v_isSharedCheck_6273_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6264_)) as u8;
                                    if v_isSharedCheck_6273_ == 0 {
                                        v___x_6268_ = v___x_6264_;
                                        v_isShared_6269_ = v_isSharedCheck_6273_;
                                        state = 69;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6266_);
                                        crate::leanh::lean_dec(v___x_6264_);
                                        v___x_6268_ = crate::leanh::lean_box(0);
                                        v_isShared_6269_ = v_isSharedCheck_6273_;
                                        state = 69;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
                1 => {
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                    crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                    crate::leanh::lean_dec_ref(v_leanOpts_5897_);
                    crate::leanh::lean_dec(v_args_5853_);
                    v___x_6274_ = lean_array_to_list(v_forwardedArgs_5898_);
                    v___x_6275_ = l_Lean_Server_Watchdog_watchdogMain(v___x_6274_);
                    return v___x_6275_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_errorOnKinds_5914_);
                    crate::leanh::lean_dec(v_bcFileName_x3f_5912_);
                    crate::leanh::lean_dec(v_rustFileName_x3f_5911_);
                    crate::leanh::lean_dec(v_ileanFileName_x3f_5910_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_5909_);
                    crate::leanh::lean_dec(v_setupFileName_x3f_5908_);
                    crate::leanh::lean_dec(v_rootDir_x3f_5907_);
                    crate::leanh::lean_dec_ref(v_forwardedArgs_5898_);
                    crate::leanh::lean_dec(v_args_5853_);
                    v___x_6276_ = l_Lean_Server_FileWorker_workerMain(v_leanOpts_5897_);
                    return v___x_6276_;
                }
            },
            69 => {
                if v_isShared_6269_ == 0 {
                    v___x_6271_ = v___x_6268_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_6272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6272_, 0, v_a_6266_);
                    v___x_6271_ = v_reuseFailAlloc_6272_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_6271_;
            }
            71 => {
                v___x_6278_ = l___private_Lean_Shell_0__Lean_timeout;
                v_timeout_6279_ =
                    l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(
                        v_leanOpts_5897_,
                        v___x_6278_,
                    );
                v___x_6280_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6281_ = lean_nat_dec_eq(v_timeout_6279_, v___x_6280_);
                if v___x_6281_ == 0 {
                    v___x_6282_ = lean_usize_of_nat(v_timeout_6279_);
                    crate::leanh::lean_dec(v_timeout_6279_);
                    v___x_6283_ = 1000usize;
                    v___x_6284_ = lean_usize_mul(v___x_6282_, v___x_6283_);
                    v___x_6285_ = lean_internal_set_max_heartbeat(v___x_6284_);
                    state = 68;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_timeout_6279_);
                    state = 68;
                    continue;
                }
            }
            72 => {
                v___x_6303_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_6302_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6301_, 0, v___x_6303_);
                    v___x_6305_ = v___x_6301_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_6306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6306_, 0, v___x_6303_);
                    v___x_6305_ = v_reuseFailAlloc_6306_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_6305_;
            }
            74 => {
                if v_isShared_6312_ == 0 {
                    v___x_6314_ = v___x_6311_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_6315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6315_, 0, v_a_6309_);
                    v___x_6314_ = v_reuseFailAlloc_6315_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                return v___x_6314_;
            }
            76 => {
                if v_isShared_6320_ == 0 {
                    v___x_6322_ = v___x_6319_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_6323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6323_, 0, v_a_6317_);
                    v___x_6322_ = v_reuseFailAlloc_6323_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_6322_;
            }
            78 => {
                if v_isShared_6328_ == 0 {
                    v___x_6330_ = v___x_6327_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_6331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6331_, 0, v_a_6325_);
                    v___x_6330_ = v_reuseFailAlloc_6331_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_6330_;
            }
            80 => {
                v___x_6339_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
                if v_isShared_6338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6337_, 0, v___x_6339_);
                    v___x_6341_ = v___x_6337_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_6342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6342_, 0, v___x_6339_);
                    v___x_6341_ = v_reuseFailAlloc_6342_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_6341_;
            }
            82 => {
                if v_isShared_6348_ == 0 {
                    v___x_6350_ = v___x_6347_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_6351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6351_, 0, v_a_6345_);
                    v___x_6350_ = v_reuseFailAlloc_6351_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                return v___x_6350_;
            }
            84 => {
                if v_isShared_6356_ == 0 {
                    v___x_6358_ = v___x_6355_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_6359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6359_, 0, v_a_6353_);
                    v___x_6358_ = v_reuseFailAlloc_6359_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                return v___x_6358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Shell_0__Lean_shellMain___boxed(
    mut v_args_6361_: *mut crate::leanh::LeanObject,
    mut v_opts_6362_: *mut crate::leanh::LeanObject,
    mut v_a_6363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6364_ = lean_shell_main(v_args_6361_, v_opts_6362_);
    return v_res_6364_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(
    mut v_val_6365_: *mut crate::leanh::LeanObject,
    mut v_inst_6366_: *mut crate::leanh::LeanObject,
    mut v_R_6367_: *mut crate::leanh::LeanObject,
    mut v_a_6368_: *mut crate::leanh::LeanObject,
    mut v_b_6369_: *mut crate::leanh::LeanObject,
    mut v_c_6370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6371_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_val_6365_, v_a_6368_, v_b_6369_);
    return v___x_6371_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(
    mut v_val_6372_: *mut crate::leanh::LeanObject,
    mut v_inst_6373_: *mut crate::leanh::LeanObject,
    mut v_R_6374_: *mut crate::leanh::LeanObject,
    mut v_a_6375_: *mut crate::leanh::LeanObject,
    mut v_b_6376_: *mut crate::leanh::LeanObject,
    mut v_c_6377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6378_ =
        l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(
            v_val_6372_,
            v_inst_6373_,
            v_R_6374_,
            v_a_6375_,
            v_b_6376_,
            v_c_6377_,
        );
    crate::leanh::lean_dec(v_b_6376_);
    crate::leanh::lean_dec_ref(v_val_6372_);
    return v_res_6378_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Shell(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Frontend(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ParseImportsFast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Watchdog(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_EmitRust(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Shell_0__Lean_shortVersionString =
        _init_l___private_Lean_Shell_0__Lean_shortVersionString();
    crate::leanh::lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString);
    l___private_Lean_Shell_0__Lean_versionHeader =
        _init_l___private_Lean_Shell_0__Lean_versionHeader();
    crate::leanh::lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader);
    l___private_Lean_Shell_0__Lean_featuresString =
        _init_l___private_Lean_Shell_0__Lean_featuresString();
    crate::leanh::lean_mark_persistent(l___private_Lean_Shell_0__Lean_featuresString);
    res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Shell_0__Lean_maxMemory = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Shell_0__Lean_maxMemory);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Shell_0__Lean_timeout = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Shell_0__Lean_timeout);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Shell_0__Lean_verbose = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Shell_0__Lean_verbose);
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Shell_0__Lean_defaultTrustLevel =
        _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel();
    l___private_Lean_Shell_0__Lean_defaultNumThreads =
        _init_l___private_Lean_Shell_0__Lean_defaultNumThreads();
    l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1 =
        _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(
        );
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1,
    );
    l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1 =
        _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Shell(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Shell(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Frontend(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ParseImportsFast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_Watchdog(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_FileWorker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_EmitRust(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Shell(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Shell(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Shell(builtin);
}
