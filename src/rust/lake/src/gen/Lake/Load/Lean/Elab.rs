// Lean compiler output
// Module: Lake.Load.Lean.Elab
// Imports: Lake.Load.Config Lean.Compiler.IR.CompilerM Lean.Elab.Frontend Lake.DSL.Extensions Lake.Util.JsonObject Init.System.Platform Lake.DSL.AttributesCore
use crate::ffi::{
    lake_environment_add, lean_array_fget, lean_array_fget_borrowed, lean_array_fset,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_io_prim_handle_lock, lean_io_prim_handle_mk,
    lean_io_prim_handle_truncate, lean_io_prim_handle_try_lock, lean_io_prim_handle_unlock,
    lean_io_remove_file, lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_string_compare, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint64_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_land,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::l_String_toName;
use crate::r#gen::Init::Prelude::l_Lean_Syntax_getPos_x3f;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_fileName, l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_Handle_putStrLn, l_IO_FS_Handle_readToEnd, l_IO_FS_createDirAll, l_IO_FS_readFile,
    l_System_FilePath_pathExists,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_target,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Build::Trace::{l_Lake_Hash_fromJson_x3f, l_Lake_computeTextFileHash};
use crate::r#gen::Lake::Config::Defaults::l_Lake_defaultLakeDir;
use crate::r#gen::Lake::Config::Env::l_Lake_Env_leanGithash;
use crate::r#gen::Lake::DSL::AttributesCore::{
    initialize_Lake_DSL_AttributesCore, runtime_initialize_Lake_DSL_AttributesCore,
};
use crate::r#gen::Lake::DSL::Extensions::{
    initialize_Lake_DSL_Extensions, l_Lake_dirExt, l_Lake_nameExt, l_Lake_optsExt,
    runtime_initialize_Lake_DSL_Extensions,
};
use crate::r#gen::Lake::Load::Config::{
    initialize_Lake_Load_Config, runtime_initialize_Lake_Load_Config,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, l_Lake_JsonObject_getJson_x3f,
    runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lake::Util::Log::l_Lake_LogEntry_ofMessage;
use crate::r#gen::Lake::Util::String::l_Lake_lowerHexUInt64;
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObj_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f,
    l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_Name_fromJson_x3f;
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::l_Lean_Elab_Command_mkState;
use crate::r#gen::Lean::Elab::Frontend::{
    initialize_Lean_Elab_Frontend, l_Lean_Elab_IO_processCommands,
    runtime_initialize_Lean_Elab_Frontend,
};
use crate::r#gen::Lean::Elab::Import::l_Lean_Elab_HeaderSyntax_imports;
use crate::r#gen::Lean::Environment::{
    l_Lean_EnvExtension_setState___redArg, l_Lean_Environment_setMainModule,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_importModules,
    l_Lean_instInhabitedEnvExtensionState, l_Lean_instInhabitedPersistentEnvExtension,
    l_Lean_mkExtNameMap, l_Lean_persistentEnvExtensionsRef, l_Lean_readModuleData,
    l_Lean_writeModule, lean_mk_empty_environment,
};
use crate::r#gen::Lean::ImportingFlag::lean_enable_initializer_execution;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageLog_add, l_Lean_MessageLog_hasErrors,
};
use crate::r#gen::Lean::Parser::Extension::l_Lean_Parser_mkInputContext___redArg;
use crate::r#gen::Lean::Parser::Module::l_Lean_Parser_parseHeader;
use crate::r#gen::Lean::Setup::{l_Lean_instBEqImport_beq, l_Lean_instHashableImport_hash};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_importModulesUsingCache___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_importModulesUsingCache___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importModulesUsingCache___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0_value:
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
static mut l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_configModuleName___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 97, 107, 101, 102, 105, 108, 101, 0],
    };
static mut l_Lake_configModuleName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_configModuleName___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_configModuleName___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_configModuleName___closed__0_value)
                as *mut leanh::LeanObject,
            5060074550580813049 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_configModuleName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_configModuleName___closed__1_value) as *mut leanh::LeanObject;
pub static mut l_Lake_configModuleName: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_configModuleName___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0_value:
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
    m_fun: l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1_value:
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
        58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116,
        105, 111, 110, 32, 104, 97, 115, 32, 101, 114, 114, 111, 114, 115, 0,
    ],
};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 97, 99, 107, 97, 103, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1_value) as *mut leanh::LeanObject,659528549093005558 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 97, 99, 107, 97, 103, 101, 68, 101, 112, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4_value) as *mut leanh::LeanObject,2574662391088497709 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7_value) as *mut leanh::LeanObject,12436946493679816533 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 99, 114, 105, 112, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value) as *mut leanh::LeanObject,14767982047059385626 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 101, 102, 97, 117, 108, 116, 83, 99, 114, 105, 112, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value) as *mut leanh::LeanObject,758561379943963750 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 97, 110, 76, 105, 98, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value) as *mut leanh::LeanObject,7818855776703404064 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 97, 110, 69, 120, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value) as *mut leanh::LeanObject,11424057956103599804 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 116, 101, 114, 110, 76, 105, 98, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value) as *mut leanh::LeanObject,7509421779037782117 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 97, 114, 103, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value) as *mut leanh::LeanObject,9199123000070154982 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 101, 102, 97, 117, 108, 116, 84, 97, 114, 103, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value) as *mut leanh::LeanObject,8325663718235124360 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 115, 116, 68, 114, 105, 118, 101, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value) as *mut leanh::LeanObject,1466235757312191377 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 105, 110, 116, 68, 114, 105, 118, 101, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value) as *mut leanh::LeanObject,12055850808226400418 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [109, 111, 100, 117, 108, 101, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value) as *mut leanh::LeanObject,11171157541301760440 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [112, 97, 99, 107, 97, 103, 101, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value) as *mut leanh::LeanObject,18143559972510357022 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 105, 98, 114, 97, 114, 121, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value) as *mut leanh::LeanObject,3952046105223012164 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 111, 99, 83, 116, 114, 105, 110, 103, 69, 120, 116, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value) as *mut leanh::LeanObject,9767541092323733724 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [73, 82, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 99, 108, 77, 97, 112, 69, 120, 116, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value
) as *mut leanh::LeanObject;
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value) as *mut leanh::LeanObject,896088716302605537 as *mut leanh::LeanObject] };
pub static l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value) as *mut leanh::LeanObject,7673168519149055152 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0: u64 = 0;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 100, 120, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 108, 97, 116, 102, 111, 114, 109, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 72, 97, 115, 104, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 72, 97, 115, 104, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [111, 112, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0_value:
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
    m_fun: l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 77, 97, 112, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,12997130533650095963 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 111, 97, 100, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3_value) as *mut leanh::LeanObject,12053018533290680796 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value) as *mut leanh::LeanObject,7990409526670957309 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6_value) as *mut leanh::LeanObject,346666231919501003 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,11203482252990433206 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value) as *mut leanh::LeanObject,13483125536632994262 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 110, 102, 105, 103, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10_value) as *mut leanh::LeanObject,9590208938432260720 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0_value) as *mut leanh::LeanObject,13438747611467150932 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1_value) as *mut leanh::LeanObject,5949480926448383572 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2_value) as *mut leanh::LeanObject,17639383269484210915 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3_value) as *mut leanh::LeanObject,1417601392311464432 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4_value) as *mut leanh::LeanObject,2019991707030758114 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5_value) as *mut leanh::LeanObject,676847746840866063 as *mut leanh::LeanObject] };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0_value:
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
    m_fun: l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___lam__0___closed__0_value: leanh::LeanStringObject<108> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 108,
        m_capacity: 108,
        m_length: 107,
        m_data: [
            99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 97, 99, 113, 117, 105, 114, 101, 32, 97,
            110, 32, 101, 120, 99, 108, 117, 115, 105, 118, 101, 32, 99, 111, 110, 102, 105, 103,
            117, 114, 97, 116, 105, 111, 110, 32, 108, 111, 99, 107, 59, 32, 97, 110, 111, 116,
            104, 101, 114, 32, 112, 114, 111, 99, 101, 115, 115, 32, 109, 97, 121, 32, 97, 108,
            114, 101, 97, 100, 121, 32, 98, 101, 32, 114, 101, 99, 111, 110, 102, 105, 103, 117,
            114, 105, 110, 103, 32, 116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 0,
        ],
    };
static mut l_Lake_importConfigFile___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_importConfigFile___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_importConfigFile___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_importConfigFile___closed__0_value: leanh::LeanStringObject<32> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116,
            105, 111, 110, 32, 102, 105, 108, 101, 32, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lake_importConfigFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_importConfigFile___closed__0_value)
                as *mut leanh::LeanObject,
            3 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_importConfigFile___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [99, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lake_importConfigFile___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___closed__3_value: leanh::LeanStringObject<6> =
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
        m_data: [111, 108, 101, 97, 110, 0],
    };
static mut l_Lake_importConfigFile___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___closed__4_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [111, 108, 101, 97, 110, 46, 116, 114, 97, 99, 101, 0],
    };
static mut l_Lake_importConfigFile___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___closed__5_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [111, 108, 101, 97, 110, 46, 108, 111, 99, 107, 0],
    };
static mut l_Lake_importConfigFile___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___closed__6_value: leanh::LeanStringObject<64> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 64,
        m_capacity: 64,
        m_length: 63,
        m_data: [
            99, 111, 109, 112, 105, 108, 101, 100, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97,
            116, 105, 111, 110, 32, 105, 115, 32, 105, 110, 118, 97, 108, 105, 100, 59, 32, 114,
            117, 110, 32, 119, 105, 116, 104, 32, 39, 45, 82, 39, 32, 116, 111, 32, 114, 101, 99,
            111, 110, 102, 105, 103, 117, 114, 101, 0,
        ],
    };
static mut l_Lake_importConfigFile___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_importConfigFile___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_importConfigFile___closed__6_value)
                as *mut leanh::LeanObject,
            3 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_importConfigFile___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_importConfigFile___closed__7_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = leanh::lean_box(0);
    v___x_2456_ = leanh::lean_unsigned_to_nat(16);
    v___x_2457_ = lean_mk_array(v___x_2456_, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2458_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_);
    v___x_2459_ = leanh::lean_unsigned_to_nat(0);
    v___x_2460_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2460_, 0, v___x_2459_);
    leanh::lean_ctor_set(v___x_2460_, 1, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_);
    v___x_2463_ = lean_st_mk_ref(v___x_2462_);
    v___x_2464_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2464_, 0, v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2____boxed(
    mut v_a_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
    return v_res_2466_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4()
-> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = lean_enable_initializer_execution();
    return v___x_2468_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4___boxed(
    mut v_a_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2470_ = l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4();
    return v_res_2470_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(
    mut v_xs_2471_: *mut leanh::LeanObject,
    mut v_ys_2472_: *mut leanh::LeanObject,
    mut v_x_2473_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2475_: u8 = 0;
    let mut v_one_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2474_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2475_ = lean_nat_dec_eq(v_x_2473_, v_zero_2474_);
                if v_isZero_2475_ == 1 {
                    leanh::lean_dec(v_x_2473_);
                    return v_isZero_2475_;
                } else {
                    v_one_2476_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2477_ = lean_nat_sub(v_x_2473_, v_one_2476_);
                    leanh::lean_dec(v_x_2473_);
                    v___x_2478_ = lean_array_fget_borrowed(v_xs_2471_, v_n_2477_);
                    v___x_2479_ = lean_array_fget_borrowed(v_ys_2472_, v_n_2477_);
                    v___x_2480_ = l_Lean_instBEqImport_beq(v___x_2478_, v___x_2479_);
                    if v___x_2480_ == 0 {
                        leanh::lean_dec(v_n_2477_);
                        return v___x_2480_;
                    } else {
                        v_x_2473_ = v_n_2477_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_xs_2482_: *mut leanh::LeanObject,
    mut v_ys_2483_: *mut leanh::LeanObject,
    mut v_x_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2485_: u8 = 0;
    let mut v_r_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2485_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_2482_, v_ys_2483_, v_x_2484_);
    leanh::lean_dec_ref(v_ys_2483_);
    leanh::lean_dec_ref(v_xs_2482_);
    v_r_2486_ = leanh::lean_box((v_res_2485_) as usize);
    return v_r_2486_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(
    mut v_a_2487_: *mut leanh::LeanObject,
    mut v_b_2488_: *mut leanh::LeanObject,
    mut v_x_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2495_: u8 = 0;
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2489_) == 0 {
                    leanh::lean_dec(v_b_2488_);
                    leanh::lean_dec_ref(v_a_2487_);
                    return v_x_2489_;
                } else {
                    v_key_2490_ = leanh::lean_ctor_get(v_x_2489_, 0);
                    v_value_2491_ = leanh::lean_ctor_get(v_x_2489_, 1);
                    v_tail_2492_ = leanh::lean_ctor_get(v_x_2489_, 2);
                    v_isSharedCheck_2506_ = (!leanh::lean_is_exclusive(v_x_2489_)) as u8;
                    if v_isSharedCheck_2506_ == 0 {
                        v___x_2494_ = v_x_2489_;
                        v_isShared_2495_ = v_isSharedCheck_2506_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2492_);
                        leanh::lean_inc(v_value_2491_);
                        leanh::lean_inc(v_key_2490_);
                        leanh::lean_dec(v_x_2489_);
                        v___x_2494_ = leanh::lean_box(0);
                        v_isShared_2495_ = v_isSharedCheck_2506_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2501_ = lean_array_get_size(v_key_2490_);
                v___x_2502_ = lean_array_get_size(v_a_2487_);
                v___x_2503_ = lean_nat_dec_eq(v___x_2501_, v___x_2502_);
                if v___x_2503_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_2504_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_2490_, v_a_2487_, v___x_2501_);
                    if v___x_2504_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2494_);
                        leanh::lean_dec(v_value_2491_);
                        leanh::lean_dec(v_key_2490_);
                        v___x_2505_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2505_, 0, v_a_2487_);
                        leanh::lean_ctor_set(v___x_2505_, 1, v_b_2488_);
                        leanh::lean_ctor_set(v___x_2505_, 2, v_tail_2492_);
                        return v___x_2505_;
                    }
                }
            }
            2 => {
                v___x_2497_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_2487_, v_b_2488_, v_tail_2492_);
                if v_isShared_2495_ == 0 {
                    leanh::lean_ctor_set(v___x_2494_, 2, v___x_2497_);
                    v___x_2499_ = v___x_2494_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_key_2490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_value_2491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 2, v___x_2497_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(
    mut v_a_2507_: *mut leanh::LeanObject,
    mut v_x_2508_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2509_: u8 = 0;
    let mut v_key_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2508_) == 0 {
                    v___x_2509_ = 0;
                    return v___x_2509_;
                } else {
                    v_key_2510_ = leanh::lean_ctor_get(v_x_2508_, 0);
                    v_tail_2511_ = leanh::lean_ctor_get(v_x_2508_, 2);
                    v___x_2512_ = lean_array_get_size(v_key_2510_);
                    v___x_2513_ = lean_array_get_size(v_a_2507_);
                    v___x_2514_ = lean_nat_dec_eq(v___x_2512_, v___x_2513_);
                    if v___x_2514_ == 0 {
                        v_x_2508_ = v_tail_2511_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2516_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_2510_, v_a_2507_, v___x_2512_);
                        if v___x_2516_ == 0 {
                            v_x_2508_ = v_tail_2511_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2516_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg___boxed(
    mut v_a_2518_: *mut leanh::LeanObject,
    mut v_x_2519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2520_: u8 = 0;
    let mut v_r_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_2518_, v_x_2519_);
    leanh::lean_dec(v_x_2519_);
    leanh::lean_dec_ref(v_a_2518_);
    v_r_2521_ = leanh::lean_box((v_res_2520_) as usize);
    return v_r_2521_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(
    mut v_as_2522_: *mut leanh::LeanObject,
    mut v_i_2523_: usize,
    mut v_stop_2524_: usize,
    mut v_b_2525_: u64,
) -> u64 {
    let mut v___x_2526_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u64 = 0;
    let mut v___x_2529_: u64 = 0;
    let mut v___x_2530_: usize = 0;
    let mut v___x_2531_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2526_ = lean_usize_dec_eq(v_i_2523_, v_stop_2524_);
                if v___x_2526_ == 0 {
                    v___x_2527_ = lean_array_uget_borrowed(v_as_2522_, v_i_2523_);
                    v___x_2528_ = l_Lean_instHashableImport_hash(v___x_2527_);
                    v___x_2529_ = lean_uint64_mix_hash(v_b_2525_, v___x_2528_);
                    v___x_2530_ = 1usize;
                    v___x_2531_ = lean_usize_add(v_i_2523_, v___x_2530_);
                    v_i_2523_ = v___x_2531_;
                    v_b_2525_ = v___x_2529_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2525_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1___boxed(
    mut v_as_2533_: *mut leanh::LeanObject,
    mut v_i_2534_: *mut leanh::LeanObject,
    mut v_stop_2535_: *mut leanh::LeanObject,
    mut v_b_2536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2537_: usize = 0;
    let mut v_stop_boxed_2538_: usize = 0;
    let mut v_b_boxed_2539_: u64 = 0;
    let mut v_res_2540_: u64 = 0;
    let mut v_r_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2537_ = leanh::lean_unbox_usize(v_i_2534_);
    leanh::lean_dec(v_i_2534_);
    v_stop_boxed_2538_ = leanh::lean_unbox_usize(v_stop_2535_);
    leanh::lean_dec(v_stop_2535_);
    v_b_boxed_2539_ = leanh::lean_unbox_uint64(v_b_2536_);
    leanh::lean_dec_ref(v_b_2536_);
    v_res_2540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_as_2533_, v_i_boxed_2537_, v_stop_boxed_2538_, v_b_boxed_2539_);
    leanh::lean_dec_ref(v_as_2533_);
    v_r_2541_ = leanh::lean_box_uint64(v_res_2540_);
    return v_r_2541_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(
    mut v_x_2542_: *mut leanh::LeanObject,
    mut v_x_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2549_: u8 = 0;
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2552_: u64 = 0;
    let mut v___x_2553_: u64 = 0;
    let mut v___x_2554_: u64 = 0;
    let mut v_fold_2555_: u64 = 0;
    let mut v___x_2556_: u64 = 0;
    let mut v___x_2557_: u64 = 0;
    let mut v___x_2558_: u64 = 0;
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: usize = 0;
    let mut v___x_2561_: usize = 0;
    let mut v___x_2562_: usize = 0;
    let mut v___x_2563_: usize = 0;
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u64 = 0;
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: usize = 0;
    let mut v___x_2576_: usize = 0;
    let mut v___x_2577_: u64 = 0;
    let mut v___x_2578_: usize = 0;
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: u64 = 0;
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2543_) == 0 {
                    return v_x_2542_;
                } else {
                    v_key_2544_ = leanh::lean_ctor_get(v_x_2543_, 0);
                    v_value_2545_ = leanh::lean_ctor_get(v_x_2543_, 1);
                    v_tail_2546_ = leanh::lean_ctor_get(v_x_2543_, 2);
                    v_isSharedCheck_2581_ = (!leanh::lean_is_exclusive(v_x_2543_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v___x_2548_ = v_x_2543_;
                        v_isShared_2549_ = v_isSharedCheck_2581_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2546_);
                        leanh::lean_inc(v_value_2545_);
                        leanh::lean_inc(v_key_2544_);
                        leanh::lean_dec(v_x_2543_);
                        v___x_2548_ = leanh::lean_box(0);
                        v_isShared_2549_ = v_isSharedCheck_2581_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2550_ = lean_array_get_size(v_x_2542_);
                v___x_2570_ = 7u64;
                v___x_2571_ = leanh::lean_unsigned_to_nat(0);
                v___x_2572_ = lean_array_get_size(v_key_2544_);
                v___x_2573_ = lean_nat_dec_lt(v___x_2571_, v___x_2572_);
                if v___x_2573_ == 0 {
                    v___y_2552_ = v___x_2570_;
                    state = 2;
                    continue;
                } else {
                    v___x_2574_ = lean_nat_dec_le(v___x_2572_, v___x_2572_);
                    if v___x_2574_ == 0 {
                        if v___x_2573_ == 0 {
                            v___y_2552_ = v___x_2570_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2575_ = 0usize;
                            v___x_2576_ = lean_usize_of_nat(v___x_2572_);
                            v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_key_2544_, v___x_2575_, v___x_2576_, v___x_2570_);
                            v___y_2552_ = v___x_2577_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2578_ = 0usize;
                        v___x_2579_ = lean_usize_of_nat(v___x_2572_);
                        v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_key_2544_, v___x_2578_, v___x_2579_, v___x_2570_);
                        v___y_2552_ = v___x_2580_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2553_ = 32u64;
                v___x_2554_ = lean_uint64_shift_right(v___y_2552_, v___x_2553_);
                v_fold_2555_ = lean_uint64_xor(v___y_2552_, v___x_2554_);
                v___x_2556_ = 16u64;
                v___x_2557_ = lean_uint64_shift_right(v_fold_2555_, v___x_2556_);
                v___x_2558_ = lean_uint64_xor(v_fold_2555_, v___x_2557_);
                v___x_2559_ = lean_uint64_to_usize(v___x_2558_);
                v___x_2560_ = lean_usize_of_nat(v___x_2550_);
                v___x_2561_ = 1usize;
                v___x_2562_ = lean_usize_sub(v___x_2560_, v___x_2561_);
                v___x_2563_ = lean_usize_land(v___x_2559_, v___x_2562_);
                v___x_2564_ = lean_array_uget_borrowed(v_x_2542_, v___x_2563_);
                leanh::lean_inc(v___x_2564_);
                if v_isShared_2549_ == 0 {
                    leanh::lean_ctor_set(v___x_2548_, 2, v___x_2564_);
                    v___x_2566_ = v___x_2548_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_key_2544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_value_2545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 2, v___x_2564_);
                    v___x_2566_ = v_reuseFailAlloc_2569_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2567_ = lean_array_uset(v_x_2542_, v___x_2563_, v___x_2566_);
                v_x_2542_ = v___x_2567_;
                v_x_2543_ = v_tail_2546_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(
    mut v_i_2582_: *mut leanh::LeanObject,
    mut v_source_2583_: *mut leanh::LeanObject,
    mut v_target_2584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: u8 = 0;
    let mut v_es_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2585_ = lean_array_get_size(v_source_2583_);
                v___x_2586_ = lean_nat_dec_lt(v_i_2582_, v___x_2585_);
                if v___x_2586_ == 0 {
                    leanh::lean_dec_ref(v_source_2583_);
                    leanh::lean_dec(v_i_2582_);
                    return v_target_2584_;
                } else {
                    v_es_2587_ = lean_array_fget(v_source_2583_, v_i_2582_);
                    v___x_2588_ = leanh::lean_box(0);
                    v_source_2589_ = lean_array_fset(v_source_2583_, v_i_2582_, v___x_2588_);
                    v_target_2590_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_target_2584_, v_es_2587_);
                    v___x_2591_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2592_ = lean_nat_add(v_i_2582_, v___x_2591_);
                    leanh::lean_dec(v_i_2582_);
                    v_i_2582_ = v___x_2592_;
                    v_source_2583_ = v_source_2589_;
                    v_target_2584_ = v_target_2590_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(
    mut v_data_2594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2595_ = lean_array_get_size(v_data_2594_);
    v___x_2596_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2597_ = lean_nat_mul(v___x_2595_, v___x_2596_);
    v___x_2598_ = leanh::lean_unsigned_to_nat(0);
    v___x_2599_ = leanh::lean_box(0);
    v___x_2600_ = lean_mk_array(v_nbuckets_2597_, v___x_2599_);
    v___x_2601_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v___x_2598_, v_data_2594_, v___x_2600_);
    return v___x_2601_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(
    mut v_m_2602_: *mut leanh::LeanObject,
    mut v_a_2603_: *mut leanh::LeanObject,
    mut v_b_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: u64 = 0;
    let mut v___x_2613_: u64 = 0;
    let mut v___x_2614_: u64 = 0;
    let mut v_fold_2615_: u64 = 0;
    let mut v___x_2616_: u64 = 0;
    let mut v___x_2617_: u64 = 0;
    let mut v___x_2618_: u64 = 0;
    let mut v___x_2619_: usize = 0;
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: usize = 0;
    let mut v___x_2623_: usize = 0;
    let mut v_bkt_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: u8 = 0;
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    let mut v_val_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u64 = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: u8 = 0;
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2657_: u64 = 0;
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: usize = 0;
    let mut v___x_2660_: u64 = 0;
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2605_ = leanh::lean_ctor_get(v_m_2602_, 0);
                v_buckets_2606_ = leanh::lean_ctor_get(v_m_2602_, 1);
                v_isSharedCheck_2661_ = (!leanh::lean_is_exclusive(v_m_2602_)) as u8;
                if v_isSharedCheck_2661_ == 0 {
                    v___x_2608_ = v_m_2602_;
                    v_isShared_2609_ = v_isSharedCheck_2661_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2606_);
                    leanh::lean_inc(v_size_2605_);
                    leanh::lean_dec(v_m_2602_);
                    v___x_2608_ = leanh::lean_box(0);
                    v_isShared_2609_ = v_isSharedCheck_2661_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2610_ = lean_array_get_size(v_buckets_2606_);
                v___x_2650_ = 7u64;
                v___x_2651_ = leanh::lean_unsigned_to_nat(0);
                v___x_2652_ = lean_array_get_size(v_a_2603_);
                v___x_2653_ = lean_nat_dec_lt(v___x_2651_, v___x_2652_);
                if v___x_2653_ == 0 {
                    v___y_2612_ = v___x_2650_;
                    state = 2;
                    continue;
                } else {
                    v___x_2654_ = lean_nat_dec_le(v___x_2652_, v___x_2652_);
                    if v___x_2654_ == 0 {
                        if v___x_2653_ == 0 {
                            v___y_2612_ = v___x_2650_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2655_ = 0usize;
                            v___x_2656_ = lean_usize_of_nat(v___x_2652_);
                            v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_2603_, v___x_2655_, v___x_2656_, v___x_2650_);
                            v___y_2612_ = v___x_2657_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2658_ = 0usize;
                        v___x_2659_ = lean_usize_of_nat(v___x_2652_);
                        v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_2603_, v___x_2658_, v___x_2659_, v___x_2650_);
                        v___y_2612_ = v___x_2660_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2613_ = 32u64;
                v___x_2614_ = lean_uint64_shift_right(v___y_2612_, v___x_2613_);
                v_fold_2615_ = lean_uint64_xor(v___y_2612_, v___x_2614_);
                v___x_2616_ = 16u64;
                v___x_2617_ = lean_uint64_shift_right(v_fold_2615_, v___x_2616_);
                v___x_2618_ = lean_uint64_xor(v_fold_2615_, v___x_2617_);
                v___x_2619_ = lean_uint64_to_usize(v___x_2618_);
                v___x_2620_ = lean_usize_of_nat(v___x_2610_);
                v___x_2621_ = 1usize;
                v___x_2622_ = lean_usize_sub(v___x_2620_, v___x_2621_);
                v___x_2623_ = lean_usize_land(v___x_2619_, v___x_2622_);
                v_bkt_2624_ = lean_array_uget_borrowed(v_buckets_2606_, v___x_2623_);
                v___x_2625_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_2603_, v_bkt_2624_);
                if v___x_2625_ == 0 {
                    v___x_2626_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2627_ = lean_nat_add(v_size_2605_, v___x_2626_);
                    leanh::lean_dec(v_size_2605_);
                    leanh::lean_inc(v_bkt_2624_);
                    v___x_2628_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2628_, 0, v_a_2603_);
                    leanh::lean_ctor_set(v___x_2628_, 1, v_b_2604_);
                    leanh::lean_ctor_set(v___x_2628_, 2, v_bkt_2624_);
                    v_buckets_x27_2629_ =
                        lean_array_uset(v_buckets_2606_, v___x_2623_, v___x_2628_);
                    v___x_2630_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2631_ = lean_nat_mul(v_size_x27_2627_, v___x_2630_);
                    v___x_2632_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2633_ = lean_nat_div(v___x_2631_, v___x_2632_);
                    leanh::lean_dec(v___x_2631_);
                    v___x_2634_ = lean_array_get_size(v_buckets_x27_2629_);
                    v___x_2635_ = lean_nat_dec_le(v___x_2633_, v___x_2634_);
                    leanh::lean_dec(v___x_2633_);
                    if v___x_2635_ == 0 {
                        v_val_2636_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_buckets_x27_2629_);
                        if v_isShared_2609_ == 0 {
                            leanh::lean_ctor_set(v___x_2608_, 1, v_val_2636_);
                            leanh::lean_ctor_set(v___x_2608_, 0, v_size_x27_2627_);
                            v___x_2638_ = v___x_2608_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2639_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2639_,
                                0,
                                v_size_x27_2627_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_val_2636_);
                            v___x_2638_ = v_reuseFailAlloc_2639_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2609_ == 0 {
                            leanh::lean_ctor_set(v___x_2608_, 1, v_buckets_x27_2629_);
                            leanh::lean_ctor_set(v___x_2608_, 0, v_size_x27_2627_);
                            v___x_2641_ = v___x_2608_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2642_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2642_,
                                0,
                                v_size_x27_2627_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2642_,
                                1,
                                v_buckets_x27_2629_,
                            );
                            v___x_2641_ = v_reuseFailAlloc_2642_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2624_);
                    v___x_2643_ = leanh::lean_box(0);
                    v_buckets_x27_2644_ =
                        lean_array_uset(v_buckets_2606_, v___x_2623_, v___x_2643_);
                    v___x_2645_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_2603_, v_b_2604_, v_bkt_2624_);
                    v___x_2646_ = lean_array_uset(v_buckets_x27_2644_, v___x_2623_, v___x_2645_);
                    if v_isShared_2609_ == 0 {
                        leanh::lean_ctor_set(v___x_2608_, 1, v___x_2646_);
                        v___x_2648_ = v___x_2608_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2649_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_size_2605_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2646_);
                        v___x_2648_ = v_reuseFailAlloc_2649_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2638_;
            }
            4 => {
                return v___x_2641_;
            }
            5 => {
                return v___x_2648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(
    mut v_a_2662_: *mut leanh::LeanObject,
    mut v_x_2663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2663_) == 0 {
                    v___x_2664_ = leanh::lean_box(0);
                    return v___x_2664_;
                } else {
                    v_key_2665_ = leanh::lean_ctor_get(v_x_2663_, 0);
                    v_value_2666_ = leanh::lean_ctor_get(v_x_2663_, 1);
                    v_tail_2667_ = leanh::lean_ctor_get(v_x_2663_, 2);
                    v___x_2668_ = lean_array_get_size(v_key_2665_);
                    v___x_2669_ = lean_array_get_size(v_a_2662_);
                    v___x_2670_ = lean_nat_dec_eq(v___x_2668_, v___x_2669_);
                    if v___x_2670_ == 0 {
                        v_x_2663_ = v_tail_2667_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2672_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_2665_, v_a_2662_, v___x_2668_);
                        if v___x_2672_ == 0 {
                            v_x_2663_ = v_tail_2667_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc(v_value_2666_);
                            v___x_2674_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2674_, 0, v_value_2666_);
                            return v___x_2674_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(
    mut v_a_2675_: *mut leanh::LeanObject,
    mut v_x_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_2675_, v_x_2676_);
    leanh::lean_dec(v_x_2676_);
    leanh::lean_dec_ref(v_a_2675_);
    return v_res_2677_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(
    mut v_m_2678_: *mut leanh::LeanObject,
    mut v_a_2679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2683_: u64 = 0;
    let mut v___x_2684_: u64 = 0;
    let mut v___x_2685_: u64 = 0;
    let mut v_fold_2686_: u64 = 0;
    let mut v___x_2687_: u64 = 0;
    let mut v___x_2688_: u64 = 0;
    let mut v___x_2689_: u64 = 0;
    let mut v___x_2690_: usize = 0;
    let mut v___x_2691_: usize = 0;
    let mut v___x_2692_: usize = 0;
    let mut v___x_2693_: usize = 0;
    let mut v___x_2694_: usize = 0;
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: u64 = 0;
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: usize = 0;
    let mut v___x_2703_: usize = 0;
    let mut v___x_2704_: u64 = 0;
    let mut v___x_2705_: usize = 0;
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2680_ = leanh::lean_ctor_get(v_m_2678_, 1);
                v___x_2681_ = lean_array_get_size(v_buckets_2680_);
                v___x_2697_ = 7u64;
                v___x_2698_ = leanh::lean_unsigned_to_nat(0);
                v___x_2699_ = lean_array_get_size(v_a_2679_);
                v___x_2700_ = lean_nat_dec_lt(v___x_2698_, v___x_2699_);
                if v___x_2700_ == 0 {
                    v___y_2683_ = v___x_2697_;
                    state = 1;
                    continue;
                } else {
                    v___x_2701_ = lean_nat_dec_le(v___x_2699_, v___x_2699_);
                    if v___x_2701_ == 0 {
                        if v___x_2700_ == 0 {
                            v___y_2683_ = v___x_2697_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2702_ = 0usize;
                            v___x_2703_ = lean_usize_of_nat(v___x_2699_);
                            v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_2679_, v___x_2702_, v___x_2703_, v___x_2697_);
                            v___y_2683_ = v___x_2704_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2705_ = 0usize;
                        v___x_2706_ = lean_usize_of_nat(v___x_2699_);
                        v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_2679_, v___x_2705_, v___x_2706_, v___x_2697_);
                        v___y_2683_ = v___x_2707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2684_ = 32u64;
                v___x_2685_ = lean_uint64_shift_right(v___y_2683_, v___x_2684_);
                v_fold_2686_ = lean_uint64_xor(v___y_2683_, v___x_2685_);
                v___x_2687_ = 16u64;
                v___x_2688_ = lean_uint64_shift_right(v_fold_2686_, v___x_2687_);
                v___x_2689_ = lean_uint64_xor(v_fold_2686_, v___x_2688_);
                v___x_2690_ = lean_uint64_to_usize(v___x_2689_);
                v___x_2691_ = lean_usize_of_nat(v___x_2681_);
                v___x_2692_ = 1usize;
                v___x_2693_ = lean_usize_sub(v___x_2691_, v___x_2692_);
                v___x_2694_ = lean_usize_land(v___x_2690_, v___x_2693_);
                v___x_2695_ = lean_array_uget_borrowed(v_buckets_2680_, v___x_2694_);
                v___x_2696_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_2679_, v___x_2695_);
                return v___x_2696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(
    mut v_m_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_2708_, v_a_2709_);
    leanh::lean_dec_ref(v_a_2709_);
    leanh::lean_dec_ref(v_m_2708_);
    return v_res_2710_;
}
pub unsafe fn l_Lake_importModulesUsingCache(
    mut v_imports_2713_: *mut leanh::LeanObject,
    mut v_opts_2714_: *mut leanh::LeanObject,
    mut v_trustLevel_2715_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2727_: u8 = 0;
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: u8 = 0;
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2732_: u8 = 0;
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2738_: u8 = 0;
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v_a_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2749_: u8 = 0;
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2717_ = l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
                v___x_2718_ = lean_st_ref_get(v___x_2717_);
                v___x_2719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v___x_2718_, v_imports_2713_);
                leanh::lean_dec(v___x_2718_);
                if leanh::lean_obj_tag(v___x_2719_) == 1 {
                    leanh::lean_dec_ref(v_opts_2714_);
                    leanh::lean_dec_ref(v_imports_2713_);
                    v_val_2720_ = leanh::lean_ctor_get(v___x_2719_, 0);
                    v_isSharedCheck_2727_ = (!leanh::lean_is_exclusive(v___x_2719_)) as u8;
                    if v_isSharedCheck_2727_ == 0 {
                        v___x_2722_ = v___x_2719_;
                        v_isShared_2723_ = v_isSharedCheck_2727_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2720_);
                        leanh::lean_dec(v___x_2719_);
                        v___x_2722_ = leanh::lean_box(0);
                        v_isShared_2723_ = v_isSharedCheck_2727_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2719_);
                    v___x_2728_ = lean_enable_initializer_execution();
                    if leanh::lean_obj_tag(v___x_2728_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2728_, 1);
                        v___x_2729_ = l_Lake_importModulesUsingCache___closed__0;
                        v___x_2730_ = 0;
                        v___x_2731_ = 1;
                        v___x_2732_ = 2;
                        v___x_2733_ = leanh::lean_box(1);
                        leanh::lean_inc_ref(v_imports_2713_);
                        v___x_2734_ = l_Lean_importModules(
                            v_imports_2713_,
                            v_opts_2714_,
                            v_trustLevel_2715_,
                            v___x_2729_,
                            v___x_2730_,
                            v___x_2731_,
                            v___x_2732_,
                            v___x_2733_,
                        );
                        if leanh::lean_obj_tag(v___x_2734_) == 0 {
                            v_a_2735_ = leanh::lean_ctor_get(v___x_2734_, 0);
                            v_isSharedCheck_2745_ =
                                (!leanh::lean_is_exclusive(v___x_2734_)) as u8;
                            if v_isSharedCheck_2745_ == 0 {
                                v___x_2737_ = v___x_2734_;
                                v_isShared_2738_ = v_isSharedCheck_2745_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2735_);
                                leanh::lean_dec(v___x_2734_);
                                v___x_2737_ = leanh::lean_box(0);
                                v_isShared_2738_ = v_isSharedCheck_2745_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_imports_2713_);
                            return v___x_2734_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_opts_2714_);
                        leanh::lean_dec_ref(v_imports_2713_);
                        v_a_2746_ = leanh::lean_ctor_get(v___x_2728_, 0);
                        v_isSharedCheck_2753_ =
                            (!leanh::lean_is_exclusive(v___x_2728_)) as u8;
                        if v_isSharedCheck_2753_ == 0 {
                            v___x_2748_ = v___x_2728_;
                            v_isShared_2749_ = v_isSharedCheck_2753_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2746_);
                            leanh::lean_dec(v___x_2728_);
                            v___x_2748_ = leanh::lean_box(0);
                            v_isShared_2749_ = v_isSharedCheck_2753_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2723_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2722_, 0);
                    v___x_2725_ = v___x_2722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2726_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_val_2720_);
                    v___x_2725_ = v_reuseFailAlloc_2726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2725_;
            }
            3 => {
                v___x_2739_ = lean_st_ref_take(v___x_2717_);
                leanh::lean_inc(v_a_2735_);
                v___x_2740_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v___x_2739_, v_imports_2713_, v_a_2735_);
                v___x_2741_ = lean_st_ref_set(v___x_2717_, v___x_2740_);
                if v_isShared_2738_ == 0 {
                    v___x_2743_ = v___x_2737_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2735_);
                    v___x_2743_ = v_reuseFailAlloc_2744_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2743_;
            }
            5 => {
                if v_isShared_2749_ == 0 {
                    v___x_2751_ = v___x_2748_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2752_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
                    v___x_2751_ = v_reuseFailAlloc_2752_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_importModulesUsingCache___boxed(
    mut v_imports_2754_: *mut leanh::LeanObject,
    mut v_opts_2755_: *mut leanh::LeanObject,
    mut v_trustLevel_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_trustLevel_boxed_2758_: u32 = 0;
    let mut v_res_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_trustLevel_boxed_2758_ = leanh::lean_unbox_uint32(v_trustLevel_2756_);
    leanh::lean_dec(v_trustLevel_2756_);
    v_res_2759_ =
        l_Lake_importModulesUsingCache(v_imports_2754_, v_opts_2755_, v_trustLevel_boxed_2758_);
    return v_res_2759_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(
    mut v_00_u03b2_2760_: *mut leanh::LeanObject,
    mut v_m_2761_: *mut leanh::LeanObject,
    mut v_a_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_2761_, v_a_2762_);
    return v___x_2763_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(
    mut v_00_u03b2_2764_: *mut leanh::LeanObject,
    mut v_m_2765_: *mut leanh::LeanObject,
    mut v_a_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(v_00_u03b2_2764_, v_m_2765_, v_a_2766_);
    leanh::lean_dec_ref(v_a_2766_);
    leanh::lean_dec_ref(v_m_2765_);
    return v_res_2767_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1(
    mut v_00_u03b2_2768_: *mut leanh::LeanObject,
    mut v_m_2769_: *mut leanh::LeanObject,
    mut v_a_2770_: *mut leanh::LeanObject,
    mut v_b_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_2769_, v_a_2770_, v_b_2771_);
    return v___x_2772_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(
    mut v_00_u03b2_2773_: *mut leanh::LeanObject,
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_x_2775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2776_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_2774_, v_x_2775_);
    return v___x_2776_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(
    mut v_00_u03b2_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
    mut v_x_2779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(v_00_u03b2_2777_, v_a_2778_, v_x_2779_);
    leanh::lean_dec(v_x_2779_);
    leanh::lean_dec_ref(v_a_2778_);
    return v_res_2780_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(
    mut v_00_u03b2_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
    mut v_x_2783_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2784_: u8 = 0;
    v___x_2784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_2782_, v_x_2783_);
    return v___x_2784_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(
    mut v_00_u03b2_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_x_2787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2788_: u8 = 0;
    let mut v_r_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2788_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_00_u03b2_2785_, v_a_2786_, v_x_2787_);
    leanh::lean_dec(v_x_2787_);
    leanh::lean_dec_ref(v_a_2786_);
    v_r_2789_ = leanh::lean_box((v_res_2788_) as usize);
    return v_r_2789_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4(
    mut v_00_u03b2_2790_: *mut leanh::LeanObject,
    mut v_data_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_data_2791_);
    return v___x_2792_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5(
    mut v_00_u03b2_2793_: *mut leanh::LeanObject,
    mut v_a_2794_: *mut leanh::LeanObject,
    mut v_b_2795_: *mut leanh::LeanObject,
    mut v_x_2796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2797_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_2794_, v_b_2795_, v_x_2796_);
    return v___x_2797_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(
    mut v_xs_2798_: *mut leanh::LeanObject,
    mut v_ys_2799_: *mut leanh::LeanObject,
    mut v_hsz_2800_: *mut leanh::LeanObject,
    mut v_x_2801_: *mut leanh::LeanObject,
    mut v_x_2802_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2803_: u8 = 0;
    v___x_2803_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_2798_, v_ys_2799_, v_x_2801_);
    return v___x_2803_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___boxed(
    mut v_xs_2804_: *mut leanh::LeanObject,
    mut v_ys_2805_: *mut leanh::LeanObject,
    mut v_hsz_2806_: *mut leanh::LeanObject,
    mut v_x_2807_: *mut leanh::LeanObject,
    mut v_x_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2809_: u8 = 0;
    let mut v_r_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(v_xs_2804_, v_ys_2805_, v_hsz_2806_, v_x_2807_, v_x_2808_);
    leanh::lean_dec_ref(v_ys_2805_);
    leanh::lean_dec_ref(v_xs_2804_);
    v_r_2810_ = leanh::lean_box((v_res_2809_) as usize);
    return v_r_2810_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6(
    mut v_00_u03b2_2811_: *mut leanh::LeanObject,
    mut v_i_2812_: *mut leanh::LeanObject,
    mut v_source_2813_: *mut leanh::LeanObject,
    mut v_target_2814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v_i_2812_, v_source_2813_, v_target_2814_);
    return v___x_2815_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7(
    mut v_00_u03b2_2816_: *mut leanh::LeanObject,
    mut v_x_2817_: *mut leanh::LeanObject,
    mut v_x_2818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_x_2817_, v_x_2818_);
    return v___x_2819_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(
    mut v_header_2821_: *mut leanh::LeanObject,
    mut v_opts_2822_: *mut leanh::LeanObject,
    mut v_inputCtx_2823_: *mut leanh::LeanObject,
    mut v_a_2824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2826_: u8 = 0;
    let mut v_imports_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u32 = 0;
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2838_: u8 = 0;
    let mut v_a_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: u8 = 0;
    let mut v___y_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u32 = 0;
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2864_: u8 = 0;
    let mut v_a_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2868_: u8 = 0;
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2872_: u8 = 0;
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2826_ = 1;
                leanh::lean_inc(v_header_2821_);
                v_imports_2827_ = l_Lean_Elab_HeaderSyntax_imports(v_header_2821_, v___x_2826_);
                v___x_2828_ = 1024;
                v___x_2829_ =
                    l_Lake_importModulesUsingCache(v_imports_2827_, v_opts_2822_, v___x_2828_);
                if leanh::lean_obj_tag(v___x_2829_) == 0 {
                    leanh::lean_dec_ref(v_inputCtx_2823_);
                    leanh::lean_dec(v_header_2821_);
                    v_a_2830_ = leanh::lean_ctor_get(v___x_2829_, 0);
                    v_isSharedCheck_2838_ = (!leanh::lean_is_exclusive(v___x_2829_)) as u8;
                    if v_isSharedCheck_2838_ == 0 {
                        v___x_2832_ = v___x_2829_;
                        v_isShared_2833_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2830_);
                        leanh::lean_dec(v___x_2829_);
                        v___x_2832_ = leanh::lean_box(0);
                        v_isShared_2833_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2839_ = leanh::lean_ctor_get(v___x_2829_, 0);
                    leanh::lean_inc(v_a_2839_);
                    leanh::lean_dec_ref_known(v___x_2829_, 1);
                    v_fileName_2840_ = leanh::lean_ctor_get(v_inputCtx_2823_, 1);
                    leanh::lean_inc_ref(v_fileName_2840_);
                    v_fileMap_2841_ = leanh::lean_ctor_get(v_inputCtx_2823_, 2);
                    leanh::lean_inc_ref(v_fileMap_2841_);
                    leanh::lean_dec_ref(v_inputCtx_2823_);
                    v___x_2842_ = 0;
                    v___x_2873_ = l_Lean_Syntax_getPos_x3f(v_header_2821_, v___x_2842_);
                    leanh::lean_dec(v_header_2821_);
                    if leanh::lean_obj_tag(v___x_2873_) == 0 {
                        v___x_2874_ = leanh::lean_unsigned_to_nat(0);
                        v___y_2844_ = v___x_2874_;
                        state = 3;
                        continue;
                    } else {
                        v_val_2875_ = leanh::lean_ctor_get(v___x_2873_, 0);
                        leanh::lean_inc(v_val_2875_);
                        leanh::lean_dec_ref_known(v___x_2873_, 1);
                        v___y_2844_ = v_val_2875_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2834_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2834_, 0, v_a_2830_);
                leanh::lean_ctor_set(v___x_2834_, 1, v_a_2824_);
                if v_isShared_2833_ == 0 {
                    leanh::lean_ctor_set(v___x_2832_, 0, v___x_2834_);
                    v___x_2836_ = v___x_2832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
                    v___x_2836_ = v_reuseFailAlloc_2837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2836_;
            }
            3 => {
                v___x_2845_ = l_Lean_FileMap_toPosition(v_fileMap_2841_, v___y_2844_);
                leanh::lean_dec(v___y_2844_);
                v___x_2846_ = leanh::lean_box(0);
                v___x_2847_ = 2;
                v___x_2848_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0;
                v___x_2849_ = lean_io_error_to_string(v_a_2839_);
                v___x_2850_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2850_, 0, v___x_2849_);
                v___x_2851_ = l_Lean_MessageData_ofFormat(v___x_2850_);
                v___x_2852_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2852_, 0, v_fileName_2840_);
                leanh::lean_ctor_set(v___x_2852_, 1, v___x_2845_);
                leanh::lean_ctor_set(v___x_2852_, 2, v___x_2846_);
                leanh::lean_ctor_set(v___x_2852_, 3, v___x_2848_);
                leanh::lean_ctor_set(v___x_2852_, 4, v___x_2851_);
                leanh::lean_ctor_set_uint8(
                    v___x_2852_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2842_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2852_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2847_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2852_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_2842_,
                );
                v___x_2853_ = 0;
                v___x_2854_ = lean_mk_empty_environment(v___x_2853_);
                if leanh::lean_obj_tag(v___x_2854_) == 0 {
                    v_a_2855_ = leanh::lean_ctor_get(v___x_2854_, 0);
                    v_isSharedCheck_2864_ = (!leanh::lean_is_exclusive(v___x_2854_)) as u8;
                    if v_isSharedCheck_2864_ == 0 {
                        v___x_2857_ = v___x_2854_;
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2855_);
                        leanh::lean_dec(v___x_2854_);
                        v___x_2857_ = leanh::lean_box(0);
                        v_isShared_2858_ = v_isSharedCheck_2864_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2852_, 5);
                    leanh::lean_dec_ref(v_a_2824_);
                    v_a_2865_ = leanh::lean_ctor_get(v___x_2854_, 0);
                    v_isSharedCheck_2872_ = (!leanh::lean_is_exclusive(v___x_2854_)) as u8;
                    if v_isSharedCheck_2872_ == 0 {
                        v___x_2867_ = v___x_2854_;
                        v_isShared_2868_ = v_isSharedCheck_2872_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2865_);
                        leanh::lean_dec(v___x_2854_);
                        v___x_2867_ = leanh::lean_box(0);
                        v_isShared_2868_ = v_isSharedCheck_2872_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2859_ = l_Lean_MessageLog_add(v___x_2852_, v_a_2824_);
                v___x_2860_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2860_, 0, v_a_2855_);
                leanh::lean_ctor_set(v___x_2860_, 1, v___x_2859_);
                if v_isShared_2858_ == 0 {
                    leanh::lean_ctor_set(v___x_2857_, 0, v___x_2860_);
                    v___x_2862_ = v___x_2857_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
                    v___x_2862_ = v_reuseFailAlloc_2863_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2862_;
            }
            6 => {
                if v_isShared_2868_ == 0 {
                    v___x_2870_ = v___x_2867_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
                    v___x_2870_ = v_reuseFailAlloc_2871_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(
    mut v_header_2876_: *mut leanh::LeanObject,
    mut v_opts_2877_: *mut leanh::LeanObject,
    mut v_inputCtx_2878_: *mut leanh::LeanObject,
    mut v_a_2879_: *mut leanh::LeanObject,
    mut v_a_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2881_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(
        v_header_2876_,
        v_opts_2877_,
        v_inputCtx_2878_,
        v_a_2879_,
    );
    return v_res_2881_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(
    mut v_x_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isSilent_2889_: u8 = 0;
    v_isSilent_2889_ = leanh::lean_ctor_get_uint8(
        v_x_2886_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_2889_ == 0 {
        let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2890_ = l_Lake_LogEntry_ofMessage(v_x_2886_);
        v___x_2891_ = leanh::lean_box(0);
        v___x_2892_ = lean_array_push(v___y_2887_, v___x_2890_);
        v___x_2893_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2893_, 0, v___x_2891_);
        leanh::lean_ctor_set(v___x_2893_, 1, v___x_2892_);
        return v___x_2893_;
    } else {
        let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_x_2886_);
        v___x_2894_ = leanh::lean_box(0);
        v___x_2895_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2895_, 0, v___x_2894_);
        leanh::lean_ctor_set(v___x_2895_, 1, v___y_2887_);
        return v___x_2895_;
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(
    mut v_x_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2899_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_2896_, v___y_2897_);
    return v_res_2899_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(
    mut v_f_2900_: *mut leanh::LeanObject,
    mut v_as_2901_: *mut leanh::LeanObject,
    mut v_i_2902_: usize,
    mut v_stop_2903_: usize,
    mut v_b_2904_: *mut leanh::LeanObject,
    mut v___y_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2907_: u8 = 0;
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: usize = 0;
    let mut v___x_2913_: usize = 0;
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2907_ = lean_usize_dec_eq(v_i_2902_, v_stop_2903_);
                if v___x_2907_ == 0 {
                    v___x_2908_ = lean_array_uget_borrowed(v_as_2901_, v_i_2902_);
                    leanh::lean_inc_ref(v_f_2900_);
                    leanh::lean_inc(v___x_2908_);
                    v___x_2909_ = leanh::lean_apply_3(
                        v_f_2900_,
                        v___x_2908_,
                        v___y_2905_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2909_) == 0 {
                        v_a_2910_ = leanh::lean_ctor_get(v___x_2909_, 0);
                        leanh::lean_inc(v_a_2910_);
                        v_a_2911_ = leanh::lean_ctor_get(v___x_2909_, 1);
                        leanh::lean_inc(v_a_2911_);
                        leanh::lean_dec_ref_known(v___x_2909_, 2);
                        v___x_2912_ = 1usize;
                        v___x_2913_ = lean_usize_add(v_i_2902_, v___x_2912_);
                        v_i_2902_ = v___x_2913_;
                        v_b_2904_ = v_a_2910_;
                        v___y_2905_ = v_a_2911_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_f_2900_);
                        return v___x_2909_;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_2900_);
                    v___x_2915_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2915_, 0, v_b_2904_);
                    leanh::lean_ctor_set(v___x_2915_, 1, v___y_2905_);
                    return v___x_2915_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(
    mut v_f_2916_: *mut leanh::LeanObject,
    mut v_as_2917_: *mut leanh::LeanObject,
    mut v_i_2918_: *mut leanh::LeanObject,
    mut v_stop_2919_: *mut leanh::LeanObject,
    mut v_b_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2923_: usize = 0;
    let mut v_stop_boxed_2924_: usize = 0;
    let mut v_res_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2923_ = leanh::lean_unbox_usize(v_i_2918_);
    leanh::lean_dec(v_i_2918_);
    v_stop_boxed_2924_ = leanh::lean_unbox_usize(v_stop_2919_);
    leanh::lean_dec(v_stop_2919_);
    v_res_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_2916_, v_as_2917_, v_i_boxed_2923_, v_stop_boxed_2924_, v_b_2920_, v___y_2921_);
    leanh::lean_dec_ref(v_as_2917_);
    return v_res_2925_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(
    mut v_f_2926_: *mut leanh::LeanObject,
    mut v_x_2927_: *mut leanh::LeanObject,
    mut v___y_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2927_) == 0 {
        let mut v_cs_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2934_: u8 = 0;
        v_cs_2930_ = leanh::lean_ctor_get(v_x_2927_, 0);
        v___x_2931_ = leanh::lean_unsigned_to_nat(0);
        v___x_2932_ = lean_array_get_size(v_cs_2930_);
        v___x_2933_ = leanh::lean_box(0);
        v___x_2934_ = lean_nat_dec_lt(v___x_2931_, v___x_2932_);
        if v___x_2934_ == 0 {
            let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_f_2926_);
            v___x_2935_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2935_, 0, v___x_2933_);
            leanh::lean_ctor_set(v___x_2935_, 1, v___y_2928_);
            return v___x_2935_;
        } else {
            let mut v___x_2936_: u8 = 0;
            v___x_2936_ = lean_nat_dec_le(v___x_2932_, v___x_2932_);
            if v___x_2936_ == 0 {
                if v___x_2934_ == 0 {
                    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v_f_2926_);
                    v___x_2937_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2937_, 0, v___x_2933_);
                    leanh::lean_ctor_set(v___x_2937_, 1, v___y_2928_);
                    return v___x_2937_;
                } else {
                    let mut v___x_2938_: usize = 0;
                    let mut v___x_2939_: usize = 0;
                    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2938_ = 0usize;
                    v___x_2939_ = lean_usize_of_nat(v___x_2932_);
                    v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_2926_, v_cs_2930_, v___x_2938_, v___x_2939_, v___x_2933_, v___y_2928_);
                    return v___x_2940_;
                }
            } else {
                let mut v___x_2941_: usize = 0;
                let mut v___x_2942_: usize = 0;
                let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2941_ = 0usize;
                v___x_2942_ = lean_usize_of_nat(v___x_2932_);
                v___x_2943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_2926_, v_cs_2930_, v___x_2941_, v___x_2942_, v___x_2933_, v___y_2928_);
                return v___x_2943_;
            }
        }
    } else {
        let mut v_vs_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2948_: u8 = 0;
        v_vs_2944_ = leanh::lean_ctor_get(v_x_2927_, 0);
        v___x_2945_ = leanh::lean_unsigned_to_nat(0);
        v___x_2946_ = lean_array_get_size(v_vs_2944_);
        v___x_2947_ = leanh::lean_box(0);
        v___x_2948_ = lean_nat_dec_lt(v___x_2945_, v___x_2946_);
        if v___x_2948_ == 0 {
            let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_f_2926_);
            v___x_2949_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2949_, 0, v___x_2947_);
            leanh::lean_ctor_set(v___x_2949_, 1, v___y_2928_);
            return v___x_2949_;
        } else {
            let mut v___x_2950_: u8 = 0;
            v___x_2950_ = lean_nat_dec_le(v___x_2946_, v___x_2946_);
            if v___x_2950_ == 0 {
                if v___x_2948_ == 0 {
                    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v_f_2926_);
                    v___x_2951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2951_, 0, v___x_2947_);
                    leanh::lean_ctor_set(v___x_2951_, 1, v___y_2928_);
                    return v___x_2951_;
                } else {
                    let mut v___x_2952_: usize = 0;
                    let mut v___x_2953_: usize = 0;
                    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2952_ = 0usize;
                    v___x_2953_ = lean_usize_of_nat(v___x_2946_);
                    v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_2926_, v_vs_2944_, v___x_2952_, v___x_2953_, v___x_2947_, v___y_2928_);
                    return v___x_2954_;
                }
            } else {
                let mut v___x_2955_: usize = 0;
                let mut v___x_2956_: usize = 0;
                let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2955_ = 0usize;
                v___x_2956_ = lean_usize_of_nat(v___x_2946_);
                v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_2926_, v_vs_2944_, v___x_2955_, v___x_2956_, v___x_2947_, v___y_2928_);
                return v___x_2957_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(
    mut v_f_2958_: *mut leanh::LeanObject,
    mut v_as_2959_: *mut leanh::LeanObject,
    mut v_i_2960_: usize,
    mut v_stop_2961_: usize,
    mut v_b_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: usize = 0;
    let mut v___x_2971_: usize = 0;
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2965_ = lean_usize_dec_eq(v_i_2960_, v_stop_2961_);
                if v___x_2965_ == 0 {
                    v___x_2966_ = lean_array_uget_borrowed(v_as_2959_, v_i_2960_);
                    leanh::lean_inc_ref(v_f_2958_);
                    v___x_2967_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_2958_, v___x_2966_, v___y_2963_);
                    if leanh::lean_obj_tag(v___x_2967_) == 0 {
                        v_a_2968_ = leanh::lean_ctor_get(v___x_2967_, 0);
                        leanh::lean_inc(v_a_2968_);
                        v_a_2969_ = leanh::lean_ctor_get(v___x_2967_, 1);
                        leanh::lean_inc(v_a_2969_);
                        leanh::lean_dec_ref_known(v___x_2967_, 2);
                        v___x_2970_ = 1usize;
                        v___x_2971_ = lean_usize_add(v_i_2960_, v___x_2970_);
                        v_i_2960_ = v___x_2971_;
                        v_b_2962_ = v_a_2968_;
                        v___y_2963_ = v_a_2969_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_f_2958_);
                        return v___x_2967_;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_2958_);
                    v___x_2973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2973_, 0, v_b_2962_);
                    leanh::lean_ctor_set(v___x_2973_, 1, v___y_2963_);
                    return v___x_2973_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_f_2974_: *mut leanh::LeanObject,
    mut v_as_2975_: *mut leanh::LeanObject,
    mut v_i_2976_: *mut leanh::LeanObject,
    mut v_stop_2977_: *mut leanh::LeanObject,
    mut v_b_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
    mut v___y_2980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2981_: usize = 0;
    let mut v_stop_boxed_2982_: usize = 0;
    let mut v_res_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2981_ = leanh::lean_unbox_usize(v_i_2976_);
    leanh::lean_dec(v_i_2976_);
    v_stop_boxed_2982_ = leanh::lean_unbox_usize(v_stop_2977_);
    leanh::lean_dec(v_stop_2977_);
    v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_2974_, v_as_2975_, v_i_boxed_2981_, v_stop_boxed_2982_, v_b_2978_, v___y_2979_);
    leanh::lean_dec_ref(v_as_2975_);
    return v_res_2983_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_f_2984_: *mut leanh::LeanObject,
    mut v_x_2985_: *mut leanh::LeanObject,
    mut v___y_2986_: *mut leanh::LeanObject,
    mut v___y_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2988_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_2984_, v_x_2985_, v___y_2986_);
    leanh::lean_dec_ref(v_x_2985_);
    return v_res_2988_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(
    mut v_f_2989_: *mut leanh::LeanObject,
    mut v_t_2990_: *mut leanh::LeanObject,
    mut v___y_2991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: usize = 0;
    let mut v___x_3012_: usize = 0;
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: usize = 0;
    let mut v___x_3015_: usize = 0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v_unused_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2993_ = leanh::lean_ctor_get(v_t_2990_, 0);
                v_tail_2994_ = leanh::lean_ctor_get(v_t_2990_, 1);
                leanh::lean_inc_ref(v_f_2989_);
                v___x_2995_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_2989_, v_root_2993_, v___y_2991_);
                if leanh::lean_obj_tag(v___x_2995_) == 0 {
                    v_a_2996_ = leanh::lean_ctor_get(v___x_2995_, 1);
                    v_isSharedCheck_3017_ = (!leanh::lean_is_exclusive(v___x_2995_)) as u8;
                    if v_isSharedCheck_3017_ == 0 {
                        v_unused_3018_ = leanh::lean_ctor_get(v___x_2995_, 0);
                        leanh::lean_dec(v_unused_3018_);
                        v___x_2998_ = v___x_2995_;
                        v_isShared_2999_ = v_isSharedCheck_3017_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2996_);
                        leanh::lean_dec(v___x_2995_);
                        v___x_2998_ = leanh::lean_box(0);
                        v_isShared_2999_ = v_isSharedCheck_3017_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_2989_);
                    return v___x_2995_;
                }
            }
            1 => {
                v___x_3000_ = leanh::lean_unsigned_to_nat(0);
                v___x_3001_ = lean_array_get_size(v_tail_2994_);
                v___x_3002_ = leanh::lean_box(0);
                v___x_3003_ = lean_nat_dec_lt(v___x_3000_, v___x_3001_);
                if v___x_3003_ == 0 {
                    leanh::lean_dec_ref(v_f_2989_);
                    if v_isShared_2999_ == 0 {
                        leanh::lean_ctor_set(v___x_2998_, 0, v___x_3002_);
                        v___x_3005_ = v___x_2998_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3006_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3002_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_a_2996_);
                        v___x_3005_ = v_reuseFailAlloc_3006_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3007_ = lean_nat_dec_le(v___x_3001_, v___x_3001_);
                    if v___x_3007_ == 0 {
                        if v___x_3003_ == 0 {
                            leanh::lean_dec_ref(v_f_2989_);
                            if v_isShared_2999_ == 0 {
                                leanh::lean_ctor_set(v___x_2998_, 0, v___x_3002_);
                                v___x_3009_ = v___x_2998_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3010_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3002_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_a_2996_);
                                v___x_3009_ = v_reuseFailAlloc_3010_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2998_);
                            v___x_3011_ = 0usize;
                            v___x_3012_ = lean_usize_of_nat(v___x_3001_);
                            v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_2989_, v_tail_2994_, v___x_3011_, v___x_3012_, v___x_3002_, v_a_2996_);
                            return v___x_3013_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2998_);
                        v___x_3014_ = 0usize;
                        v___x_3015_ = lean_usize_of_nat(v___x_3001_);
                        v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_2989_, v_tail_2994_, v___x_3014_, v___x_3015_, v___x_3002_, v_a_2996_);
                        return v___x_3016_;
                    }
                }
            }
            2 => {
                return v___x_3005_;
            }
            3 => {
                return v___x_3009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(
    mut v_f_3019_: *mut leanh::LeanObject,
    mut v_t_3020_: *mut leanh::LeanObject,
    mut v___y_3021_: *mut leanh::LeanObject,
    mut v___y_3022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3023_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_3019_, v_t_3020_, v___y_3021_);
    leanh::lean_dec_ref(v_t_3020_);
    return v_res_3023_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_3024_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(
    mut v_f_3025_: *mut leanh::LeanObject,
    mut v_x_3026_: *mut leanh::LeanObject,
    mut v_x_3027_: usize,
    mut v_x_3028_: usize,
    mut v___y_3029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: usize = 0;
    let mut v_j_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: usize = 0;
    let mut v___x_3037_: usize = 0;
    let mut v___x_3038_: usize = 0;
    let mut v___x_3039_: usize = 0;
    let mut v___x_3040_: usize = 0;
    let mut v___x_3041_: usize = 0;
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: u8 = 0;
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: usize = 0;
    let mut v___x_3060_: usize = 0;
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: usize = 0;
    let mut v___x_3063_: usize = 0;
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut v_unused_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: u8 = 0;
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: usize = 0;
    let mut v___x_3076_: usize = 0;
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: usize = 0;
    let mut v___x_3079_: usize = 0;
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3026_) == 0 {
                    v_cs_3031_ = leanh::lean_ctor_get(v_x_3026_, 0);
                    v___x_3032_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
                    v___x_3033_ = lean_usize_shift_right(v_x_3027_, v_x_3028_);
                    v_j_3034_ = lean_usize_to_nat(v___x_3033_);
                    v___x_3035_ = lean_array_get_borrowed(v___x_3032_, v_cs_3031_, v_j_3034_);
                    v___x_3036_ = 1usize;
                    v___x_3037_ = lean_usize_shift_left(v___x_3036_, v_x_3028_);
                    v___x_3038_ = lean_usize_sub(v___x_3037_, v___x_3036_);
                    v___x_3039_ = lean_usize_land(v_x_3027_, v___x_3038_);
                    v___x_3040_ = 5usize;
                    v___x_3041_ = lean_usize_sub(v_x_3028_, v___x_3040_);
                    leanh::lean_inc_ref(v_f_3025_);
                    v___x_3042_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_3025_, v___x_3035_, v___x_3039_, v___x_3041_, v___y_3029_);
                    if leanh::lean_obj_tag(v___x_3042_) == 0 {
                        v_a_3043_ = leanh::lean_ctor_get(v___x_3042_, 1);
                        v_isSharedCheck_3065_ =
                            (!leanh::lean_is_exclusive(v___x_3042_)) as u8;
                        if v_isSharedCheck_3065_ == 0 {
                            v_unused_3066_ = leanh::lean_ctor_get(v___x_3042_, 0);
                            leanh::lean_dec(v_unused_3066_);
                            v___x_3045_ = v___x_3042_;
                            v_isShared_3046_ = v_isSharedCheck_3065_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3043_);
                            leanh::lean_dec(v___x_3042_);
                            v___x_3045_ = leanh::lean_box(0);
                            v_isShared_3046_ = v_isSharedCheck_3065_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_j_3034_);
                        leanh::lean_dec_ref(v_f_3025_);
                        return v___x_3042_;
                    }
                } else {
                    v_vs_3067_ = leanh::lean_ctor_get(v_x_3026_, 0);
                    v___x_3068_ = lean_usize_to_nat(v_x_3027_);
                    v___x_3069_ = lean_array_get_size(v_vs_3067_);
                    v___x_3070_ = leanh::lean_box(0);
                    v___x_3071_ = lean_nat_dec_lt(v___x_3068_, v___x_3069_);
                    if v___x_3071_ == 0 {
                        leanh::lean_dec(v___x_3068_);
                        leanh::lean_dec_ref(v_f_3025_);
                        v___x_3072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3072_, 0, v___x_3070_);
                        leanh::lean_ctor_set(v___x_3072_, 1, v___y_3029_);
                        return v___x_3072_;
                    } else {
                        v___x_3073_ = lean_nat_dec_le(v___x_3069_, v___x_3069_);
                        if v___x_3073_ == 0 {
                            if v___x_3071_ == 0 {
                                leanh::lean_dec(v___x_3068_);
                                leanh::lean_dec_ref(v_f_3025_);
                                v___x_3074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3074_, 0, v___x_3070_);
                                leanh::lean_ctor_set(v___x_3074_, 1, v___y_3029_);
                                return v___x_3074_;
                            } else {
                                v___x_3075_ = lean_usize_of_nat(v___x_3068_);
                                leanh::lean_dec(v___x_3068_);
                                v___x_3076_ = lean_usize_of_nat(v___x_3069_);
                                v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_3025_, v_vs_3067_, v___x_3075_, v___x_3076_, v___x_3070_, v___y_3029_);
                                return v___x_3077_;
                            }
                        } else {
                            v___x_3078_ = lean_usize_of_nat(v___x_3068_);
                            leanh::lean_dec(v___x_3068_);
                            v___x_3079_ = lean_usize_of_nat(v___x_3069_);
                            v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_3025_, v_vs_3067_, v___x_3078_, v___x_3079_, v___x_3070_, v___y_3029_);
                            return v___x_3080_;
                        }
                    }
                }
            }
            1 => {
                v___x_3047_ = leanh::lean_unsigned_to_nat(1);
                v___x_3048_ = lean_nat_add(v_j_3034_, v___x_3047_);
                leanh::lean_dec(v_j_3034_);
                v___x_3049_ = lean_array_get_size(v_cs_3031_);
                v___x_3050_ = leanh::lean_box(0);
                v___x_3051_ = lean_nat_dec_lt(v___x_3048_, v___x_3049_);
                if v___x_3051_ == 0 {
                    leanh::lean_dec(v___x_3048_);
                    leanh::lean_dec_ref(v_f_3025_);
                    if v_isShared_3046_ == 0 {
                        leanh::lean_ctor_set(v___x_3045_, 0, v___x_3050_);
                        v___x_3053_ = v___x_3045_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3054_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3050_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_a_3043_);
                        v___x_3053_ = v_reuseFailAlloc_3054_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3055_ = lean_nat_dec_le(v___x_3049_, v___x_3049_);
                    if v___x_3055_ == 0 {
                        if v___x_3051_ == 0 {
                            leanh::lean_dec(v___x_3048_);
                            leanh::lean_dec_ref(v_f_3025_);
                            if v_isShared_3046_ == 0 {
                                leanh::lean_ctor_set(v___x_3045_, 0, v___x_3050_);
                                v___x_3057_ = v___x_3045_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3058_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3050_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_a_3043_);
                                v___x_3057_ = v_reuseFailAlloc_3058_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3045_);
                            v___x_3059_ = lean_usize_of_nat(v___x_3048_);
                            leanh::lean_dec(v___x_3048_);
                            v___x_3060_ = lean_usize_of_nat(v___x_3049_);
                            v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_3025_, v_cs_3031_, v___x_3059_, v___x_3060_, v___x_3050_, v_a_3043_);
                            return v___x_3061_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3045_);
                        v___x_3062_ = lean_usize_of_nat(v___x_3048_);
                        leanh::lean_dec(v___x_3048_);
                        v___x_3063_ = lean_usize_of_nat(v___x_3049_);
                        v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_3025_, v_cs_3031_, v___x_3062_, v___x_3063_, v___x_3050_, v_a_3043_);
                        return v___x_3064_;
                    }
                }
            }
            2 => {
                return v___x_3053_;
            }
            3 => {
                return v___x_3057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(
    mut v_f_3081_: *mut leanh::LeanObject,
    mut v_x_3082_: *mut leanh::LeanObject,
    mut v_x_3083_: *mut leanh::LeanObject,
    mut v_x_3084_: *mut leanh::LeanObject,
    mut v___y_3085_: *mut leanh::LeanObject,
    mut v___y_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13978__boxed_3087_: usize = 0;
    let mut v_x_13979__boxed_3088_: usize = 0;
    let mut v_res_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13978__boxed_3087_ = leanh::lean_unbox_usize(v_x_3083_);
    leanh::lean_dec(v_x_3083_);
    v_x_13979__boxed_3088_ = leanh::lean_unbox_usize(v_x_3084_);
    leanh::lean_dec(v_x_3084_);
    v_res_3089_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_3081_, v_x_3082_, v_x_13978__boxed_3087_, v_x_13979__boxed_3088_, v___y_3085_);
    leanh::lean_dec_ref(v_x_3082_);
    return v_res_3089_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(
    mut v_f_3090_: *mut leanh::LeanObject,
    mut v_t_3091_: *mut leanh::LeanObject,
    mut v_start_3092_: *mut leanh::LeanObject,
    mut v___y_3093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v_root_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3099_: usize = 0;
    let mut v_tailOff_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: usize = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: usize = 0;
    let mut v___x_3119_: usize = 0;
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: usize = 0;
    let mut v___x_3122_: usize = 0;
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_unused_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: usize = 0;
    let mut v___x_3134_: usize = 0;
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3095_ = leanh::lean_unsigned_to_nat(0);
                v___x_3096_ = lean_nat_dec_eq(v_start_3092_, v___x_3095_);
                if v___x_3096_ == 0 {
                    v_root_3097_ = leanh::lean_ctor_get(v_t_3091_, 0);
                    v_tail_3098_ = leanh::lean_ctor_get(v_t_3091_, 1);
                    v_shift_3099_ = leanh::lean_ctor_get_usize(v_t_3091_, 4);
                    v_tailOff_3100_ = leanh::lean_ctor_get(v_t_3091_, 3);
                    v___x_3101_ = lean_nat_dec_le(v_tailOff_3100_, v_start_3092_);
                    if v___x_3101_ == 0 {
                        v___x_3102_ = lean_usize_of_nat(v_start_3092_);
                        leanh::lean_inc_ref(v_f_3090_);
                        v___x_3103_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_3090_, v_root_3097_, v___x_3102_, v_shift_3099_, v___y_3093_);
                        if leanh::lean_obj_tag(v___x_3103_) == 0 {
                            v_a_3104_ = leanh::lean_ctor_get(v___x_3103_, 1);
                            v_isSharedCheck_3124_ =
                                (!leanh::lean_is_exclusive(v___x_3103_)) as u8;
                            if v_isSharedCheck_3124_ == 0 {
                                v_unused_3125_ = leanh::lean_ctor_get(v___x_3103_, 0);
                                leanh::lean_dec(v_unused_3125_);
                                v___x_3106_ = v___x_3103_;
                                v_isShared_3107_ = v_isSharedCheck_3124_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3104_);
                                leanh::lean_dec(v___x_3103_);
                                v___x_3106_ = leanh::lean_box(0);
                                v_isShared_3107_ = v_isSharedCheck_3124_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_f_3090_);
                            return v___x_3103_;
                        }
                    } else {
                        v___x_3126_ = lean_nat_sub(v_start_3092_, v_tailOff_3100_);
                        v___x_3127_ = lean_array_get_size(v_tail_3098_);
                        v___x_3128_ = leanh::lean_box(0);
                        v___x_3129_ = lean_nat_dec_lt(v___x_3126_, v___x_3127_);
                        if v___x_3129_ == 0 {
                            leanh::lean_dec(v___x_3126_);
                            leanh::lean_dec_ref(v_f_3090_);
                            v___x_3130_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3130_, 0, v___x_3128_);
                            leanh::lean_ctor_set(v___x_3130_, 1, v___y_3093_);
                            return v___x_3130_;
                        } else {
                            v___x_3131_ = lean_nat_dec_le(v___x_3127_, v___x_3127_);
                            if v___x_3131_ == 0 {
                                if v___x_3129_ == 0 {
                                    leanh::lean_dec(v___x_3126_);
                                    leanh::lean_dec_ref(v_f_3090_);
                                    v___x_3132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3132_, 0, v___x_3128_);
                                    leanh::lean_ctor_set(v___x_3132_, 1, v___y_3093_);
                                    return v___x_3132_;
                                } else {
                                    v___x_3133_ = lean_usize_of_nat(v___x_3126_);
                                    leanh::lean_dec(v___x_3126_);
                                    v___x_3134_ = lean_usize_of_nat(v___x_3127_);
                                    v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_3090_, v_tail_3098_, v___x_3133_, v___x_3134_, v___x_3128_, v___y_3093_);
                                    return v___x_3135_;
                                }
                            } else {
                                v___x_3136_ = lean_usize_of_nat(v___x_3126_);
                                leanh::lean_dec(v___x_3126_);
                                v___x_3137_ = lean_usize_of_nat(v___x_3127_);
                                v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_3090_, v_tail_3098_, v___x_3136_, v___x_3137_, v___x_3128_, v___y_3093_);
                                return v___x_3138_;
                            }
                        }
                    }
                } else {
                    v___x_3139_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_3090_, v_t_3091_, v___y_3093_);
                    return v___x_3139_;
                }
            }
            1 => {
                v___x_3108_ = lean_array_get_size(v_tail_3098_);
                v___x_3109_ = leanh::lean_box(0);
                v___x_3110_ = lean_nat_dec_lt(v___x_3095_, v___x_3108_);
                if v___x_3110_ == 0 {
                    leanh::lean_dec_ref(v_f_3090_);
                    if v_isShared_3107_ == 0 {
                        leanh::lean_ctor_set(v___x_3106_, 0, v___x_3109_);
                        v___x_3112_ = v___x_3106_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3109_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_a_3104_);
                        v___x_3112_ = v_reuseFailAlloc_3113_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3114_ = lean_nat_dec_le(v___x_3108_, v___x_3108_);
                    if v___x_3114_ == 0 {
                        if v___x_3110_ == 0 {
                            leanh::lean_dec_ref(v_f_3090_);
                            if v_isShared_3107_ == 0 {
                                leanh::lean_ctor_set(v___x_3106_, 0, v___x_3109_);
                                v___x_3116_ = v___x_3106_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3117_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3109_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3104_);
                                v___x_3116_ = v_reuseFailAlloc_3117_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3106_);
                            v___x_3118_ = 0usize;
                            v___x_3119_ = lean_usize_of_nat(v___x_3108_);
                            v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_3090_, v_tail_3098_, v___x_3118_, v___x_3119_, v___x_3109_, v_a_3104_);
                            return v___x_3120_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3106_);
                        v___x_3121_ = 0usize;
                        v___x_3122_ = lean_usize_of_nat(v___x_3108_);
                        v___x_3123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_3090_, v_tail_3098_, v___x_3121_, v___x_3122_, v___x_3109_, v_a_3104_);
                        return v___x_3123_;
                    }
                }
            }
            2 => {
                return v___x_3112_;
            }
            3 => {
                return v___x_3116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(
    mut v_f_3140_: *mut leanh::LeanObject,
    mut v_t_3141_: *mut leanh::LeanObject,
    mut v_start_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_3140_, v_t_3141_, v_start_3142_, v___y_3143_);
    leanh::lean_dec(v_start_3142_);
    leanh::lean_dec_ref(v_t_3141_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(
    mut v_log_3146_: *mut leanh::LeanObject,
    mut v_f_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unreported_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_unreported_3150_ = leanh::lean_ctor_get(v_log_3146_, 1);
    v___x_3151_ = leanh::lean_unsigned_to_nat(0);
    v___x_3152_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_3147_, v_unreported_3150_, v___x_3151_, v___y_3148_);
    return v___x_3152_;
}
pub unsafe fn l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(
    mut v_log_3153_: *mut leanh::LeanObject,
    mut v_f_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_3153_, v_f_3154_, v___y_3155_);
    leanh::lean_dec_ref(v_log_3153_);
    return v_res_3157_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(
    mut v_pkgIdx_3160_: *mut leanh::LeanObject,
    mut v_pkgName_3161_: *mut leanh::LeanObject,
    mut v_pkgDir_3162_: *mut leanh::LeanObject,
    mut v_lakeOpts_3163_: *mut leanh::LeanObject,
    mut v_leanOpts_3164_: *mut leanh::LeanObject,
    mut v_configFile_3165_: *mut leanh::LeanObject,
    mut v_a_3166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u8 = 0;
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v_snd_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3184_: u8 = 0;
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v_fst_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3223_: u8 = 0;
    let mut v___x_3224_: u8 = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: u8 = 0;
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut v_unused_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_a_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: u8 = 0;
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_a_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_a_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3168_ = l_IO_FS_readFile(v_configFile_3165_);
                if leanh::lean_obj_tag(v___x_3168_) == 0 {
                    v_a_3169_ = leanh::lean_ctor_get(v___x_3168_, 0);
                    leanh::lean_inc(v_a_3169_);
                    leanh::lean_dec_ref_known(v___x_3168_, 1);
                    v___x_3170_ = 1;
                    v___x_3171_ = lean_string_utf8_byte_size(v_a_3169_);
                    leanh::lean_inc_ref(v_configFile_3165_);
                    v___x_3172_ = l_Lean_Parser_mkInputContext___redArg(
                        v_a_3169_,
                        v_configFile_3165_,
                        v___x_3170_,
                        v___x_3171_,
                    );
                    leanh::lean_inc_ref(v___x_3172_);
                    v___x_3173_ = l_Lean_Parser_parseHeader(v___x_3172_);
                    if leanh::lean_obj_tag(v___x_3173_) == 0 {
                        v_a_3174_ = leanh::lean_ctor_get(v___x_3173_, 0);
                        v_isSharedCheck_3272_ =
                            (!leanh::lean_is_exclusive(v___x_3173_)) as u8;
                        if v_isSharedCheck_3272_ == 0 {
                            v___x_3176_ = v___x_3173_;
                            v_isShared_3177_ = v_isSharedCheck_3272_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3174_);
                            leanh::lean_dec(v___x_3173_);
                            v___x_3176_ = leanh::lean_box(0);
                            v_isShared_3177_ = v_isSharedCheck_3272_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3172_);
                        leanh::lean_dec_ref(v_configFile_3165_);
                        leanh::lean_dec_ref(v_leanOpts_3164_);
                        leanh::lean_dec(v_lakeOpts_3163_);
                        leanh::lean_dec_ref(v_pkgDir_3162_);
                        leanh::lean_dec(v_pkgName_3161_);
                        leanh::lean_dec(v_pkgIdx_3160_);
                        v_a_3273_ = leanh::lean_ctor_get(v___x_3173_, 0);
                        leanh::lean_inc(v_a_3273_);
                        leanh::lean_dec_ref_known(v___x_3173_, 1);
                        v___x_3274_ = lean_io_error_to_string(v_a_3273_);
                        v___x_3275_ = 3;
                        v___x_3276_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_3276_, 0, v___x_3274_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3276_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_3275_,
                        );
                        v___x_3277_ = lean_array_get_size(v_a_3166_);
                        v___x_3278_ = lean_array_push(v_a_3166_, v___x_3276_);
                        v___x_3279_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3279_, 0, v___x_3277_);
                        leanh::lean_ctor_set(v___x_3279_, 1, v___x_3278_);
                        return v___x_3279_;
                    }
                } else {
                    leanh::lean_dec_ref(v_configFile_3165_);
                    leanh::lean_dec_ref(v_leanOpts_3164_);
                    leanh::lean_dec(v_lakeOpts_3163_);
                    leanh::lean_dec_ref(v_pkgDir_3162_);
                    leanh::lean_dec(v_pkgName_3161_);
                    leanh::lean_dec(v_pkgIdx_3160_);
                    v_a_3280_ = leanh::lean_ctor_get(v___x_3168_, 0);
                    leanh::lean_inc(v_a_3280_);
                    leanh::lean_dec_ref_known(v___x_3168_, 1);
                    v___x_3281_ = lean_io_error_to_string(v_a_3280_);
                    v___x_3282_ = 3;
                    v___x_3283_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_3283_, 0, v___x_3281_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3283_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_3282_,
                    );
                    v___x_3284_ = lean_array_get_size(v_a_3166_);
                    v___x_3285_ = lean_array_push(v_a_3166_, v___x_3283_);
                    v___x_3286_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3286_, 0, v___x_3284_);
                    leanh::lean_ctor_set(v___x_3286_, 1, v___x_3285_);
                    return v___x_3286_;
                }
            }
            1 => {
                v_snd_3178_ = leanh::lean_ctor_get(v_a_3174_, 1);
                leanh::lean_inc(v_snd_3178_);
                v_fst_3179_ = leanh::lean_ctor_get(v_a_3174_, 0);
                leanh::lean_inc(v_fst_3179_);
                leanh::lean_dec(v_a_3174_);
                v_fst_3180_ = leanh::lean_ctor_get(v_snd_3178_, 0);
                v_snd_3181_ = leanh::lean_ctor_get(v_snd_3178_, 1);
                v_isSharedCheck_3271_ = (!leanh::lean_is_exclusive(v_snd_3178_)) as u8;
                if v_isSharedCheck_3271_ == 0 {
                    v___x_3183_ = v_snd_3178_;
                    v_isShared_3184_ = v_isSharedCheck_3271_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3181_);
                    leanh::lean_inc(v_fst_3180_);
                    leanh::lean_dec(v_snd_3178_);
                    v___x_3183_ = leanh::lean_box(0);
                    v_isShared_3184_ = v_isSharedCheck_3271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3172_);
                leanh::lean_inc_ref(v_leanOpts_3164_);
                v___x_3185_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(
                    v_fst_3179_,
                    v_leanOpts_3164_,
                    v___x_3172_,
                    v_snd_3181_,
                );
                if leanh::lean_obj_tag(v___x_3185_) == 0 {
                    v_a_3186_ = leanh::lean_ctor_get(v___x_3185_, 0);
                    v_isSharedCheck_3261_ = (!leanh::lean_is_exclusive(v___x_3185_)) as u8;
                    if v_isSharedCheck_3261_ == 0 {
                        v___x_3188_ = v___x_3185_;
                        v_isShared_3189_ = v_isSharedCheck_3261_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3186_);
                        leanh::lean_dec(v___x_3185_);
                        v___x_3188_ = leanh::lean_box(0);
                        v_isShared_3189_ = v_isSharedCheck_3261_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_3180_);
                    leanh::lean_del_object(v___x_3176_);
                    leanh::lean_dec_ref(v___x_3172_);
                    leanh::lean_dec_ref(v_configFile_3165_);
                    leanh::lean_dec_ref(v_leanOpts_3164_);
                    leanh::lean_dec(v_lakeOpts_3163_);
                    leanh::lean_dec_ref(v_pkgDir_3162_);
                    leanh::lean_dec(v_pkgName_3161_);
                    leanh::lean_dec(v_pkgIdx_3160_);
                    v_a_3262_ = leanh::lean_ctor_get(v___x_3185_, 0);
                    leanh::lean_inc(v_a_3262_);
                    leanh::lean_dec_ref_known(v___x_3185_, 1);
                    v___x_3263_ = lean_io_error_to_string(v_a_3262_);
                    v___x_3264_ = 3;
                    v___x_3265_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_3265_, 0, v___x_3263_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3265_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_3264_,
                    );
                    v___x_3266_ = lean_array_get_size(v_a_3166_);
                    v___x_3267_ = lean_array_push(v_a_3166_, v___x_3265_);
                    if v_isShared_3184_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3183_, 1);
                        leanh::lean_ctor_set(v___x_3183_, 1, v___x_3267_);
                        leanh::lean_ctor_set(v___x_3183_, 0, v___x_3266_);
                        v___x_3269_ = v___x_3183_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3270_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3266_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 1, v___x_3267_);
                        v___x_3269_ = v_reuseFailAlloc_3270_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_3190_ = leanh::lean_ctor_get(v_a_3186_, 0);
                v_snd_3191_ = leanh::lean_ctor_get(v_a_3186_, 1);
                v_isSharedCheck_3260_ = (!leanh::lean_is_exclusive(v_a_3186_)) as u8;
                if v_isSharedCheck_3260_ == 0 {
                    v___x_3193_ = v_a_3186_;
                    v_isShared_3194_ = v_isSharedCheck_3260_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3191_);
                    leanh::lean_inc(v_fst_3190_);
                    leanh::lean_dec(v_a_3186_);
                    v___x_3193_ = leanh::lean_box(0);
                    v_isShared_3194_ = v_isSharedCheck_3260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3195_ = l_Lake_nameExt;
                v_asyncMode_3196_ = leanh::lean_ctor_get(v___x_3195_, 2);
                v___x_3197_ = l_Lake_dirExt;
                v_asyncMode_3198_ = leanh::lean_ctor_get(v___x_3197_, 2);
                v___x_3199_ = l_Lake_optsExt;
                v_asyncMode_3200_ = leanh::lean_ctor_get(v___x_3199_, 2);
                v___x_3201_ = l_Lake_configModuleName;
                v___x_3202_ = l_Lean_Environment_setMainModule(v_fst_3190_, v___x_3201_);
                if v_isShared_3194_ == 0 {
                    leanh::lean_ctor_set(v___x_3193_, 1, v_pkgName_3161_);
                    leanh::lean_ctor_set(v___x_3193_, 0, v_pkgIdx_3160_);
                    v___x_3204_ = v___x_3193_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_pkgIdx_3160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_pkgName_3161_);
                    v___x_3204_ = v_reuseFailAlloc_3259_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3205_ = l_Lean_EnvExtension_setState___redArg(
                    v___x_3195_,
                    v___x_3202_,
                    v___x_3204_,
                    v_asyncMode_3196_,
                );
                if v_isShared_3189_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3188_, 1);
                    leanh::lean_ctor_set(v___x_3188_, 0, v_pkgDir_3162_);
                    v___x_3207_ = v___x_3188_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_pkgDir_3162_);
                    v___x_3207_ = v_reuseFailAlloc_3258_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3208_ = l_Lean_EnvExtension_setState___redArg(
                    v___x_3197_,
                    v___x_3205_,
                    v___x_3207_,
                    v_asyncMode_3198_,
                );
                if v_isShared_3177_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3176_, 1);
                    leanh::lean_ctor_set(v___x_3176_, 0, v_lakeOpts_3163_);
                    v___x_3210_ = v___x_3176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3257_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_lakeOpts_3163_);
                    v___x_3210_ = v_reuseFailAlloc_3257_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3211_ = l_Lean_EnvExtension_setState___redArg(
                    v___x_3199_,
                    v___x_3208_,
                    v___x_3210_,
                    v_asyncMode_3200_,
                );
                v___x_3212_ =
                    l_Lean_Elab_Command_mkState(v___x_3211_, v_snd_3191_, v_leanOpts_3164_);
                v___x_3213_ = l_Lean_Elab_IO_processCommands(v___x_3172_, v_fst_3180_, v___x_3212_);
                if leanh::lean_obj_tag(v___x_3213_) == 0 {
                    leanh::lean_del_object(v___x_3183_);
                    v_a_3214_ = leanh::lean_ctor_get(v___x_3213_, 0);
                    leanh::lean_inc(v_a_3214_);
                    leanh::lean_dec_ref_known(v___x_3213_, 1);
                    v_commandState_3215_ = leanh::lean_ctor_get(v_a_3214_, 0);
                    leanh::lean_inc_ref(v_commandState_3215_);
                    leanh::lean_dec(v_a_3214_);
                    v_env_3216_ = leanh::lean_ctor_get(v_commandState_3215_, 0);
                    leanh::lean_inc_ref(v_env_3216_);
                    v_messages_3217_ = leanh::lean_ctor_get(v_commandState_3215_, 1);
                    leanh::lean_inc_ref(v_messages_3217_);
                    leanh::lean_dec_ref(v_commandState_3215_);
                    v___f_3218_ =
                        l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0;
                    v___x_3219_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_3217_, v___f_3218_, v_a_3166_);
                    if leanh::lean_obj_tag(v___x_3219_) == 0 {
                        v_a_3220_ = leanh::lean_ctor_get(v___x_3219_, 1);
                        v_isSharedCheck_3237_ =
                            (!leanh::lean_is_exclusive(v___x_3219_)) as u8;
                        if v_isSharedCheck_3237_ == 0 {
                            v_unused_3238_ = leanh::lean_ctor_get(v___x_3219_, 0);
                            leanh::lean_dec(v_unused_3238_);
                            v___x_3222_ = v___x_3219_;
                            v_isShared_3223_ = v_isSharedCheck_3237_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3220_);
                            leanh::lean_dec(v___x_3219_);
                            v___x_3222_ = leanh::lean_box(0);
                            v_isShared_3223_ = v_isSharedCheck_3237_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_messages_3217_);
                        leanh::lean_dec_ref(v_env_3216_);
                        leanh::lean_dec_ref(v_configFile_3165_);
                        v_a_3239_ = leanh::lean_ctor_get(v___x_3219_, 0);
                        v_a_3240_ = leanh::lean_ctor_get(v___x_3219_, 1);
                        v_isSharedCheck_3247_ =
                            (!leanh::lean_is_exclusive(v___x_3219_)) as u8;
                        if v_isSharedCheck_3247_ == 0 {
                            v___x_3242_ = v___x_3219_;
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3240_);
                            leanh::lean_inc(v_a_3239_);
                            leanh::lean_dec(v___x_3219_);
                            v___x_3242_ = leanh::lean_box(0);
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_configFile_3165_);
                    v_a_3248_ = leanh::lean_ctor_get(v___x_3213_, 0);
                    leanh::lean_inc(v_a_3248_);
                    leanh::lean_dec_ref_known(v___x_3213_, 1);
                    v___x_3249_ = lean_io_error_to_string(v_a_3248_);
                    v___x_3250_ = 3;
                    v___x_3251_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_3251_, 0, v___x_3249_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3251_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_3250_,
                    );
                    v___x_3252_ = lean_array_get_size(v_a_3166_);
                    v___x_3253_ = lean_array_push(v_a_3166_, v___x_3251_);
                    if v_isShared_3184_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3183_, 1);
                        leanh::lean_ctor_set(v___x_3183_, 1, v___x_3253_);
                        leanh::lean_ctor_set(v___x_3183_, 0, v___x_3252_);
                        v___x_3255_ = v___x_3183_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3256_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3252_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3253_);
                        v___x_3255_ = v_reuseFailAlloc_3256_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3224_ = l_Lean_MessageLog_hasErrors(v_messages_3217_);
                leanh::lean_dec_ref(v_messages_3217_);
                if v___x_3224_ == 0 {
                    leanh::lean_dec_ref(v_configFile_3165_);
                    if v_isShared_3223_ == 0 {
                        leanh::lean_ctor_set(v___x_3222_, 0, v_env_3216_);
                        v___x_3226_ = v___x_3222_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3227_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_env_3216_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_a_3220_);
                        v___x_3226_ = v_reuseFailAlloc_3227_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3216_);
                    v___x_3228_ =
                        l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1;
                    v___x_3229_ = lean_string_append(v_configFile_3165_, v___x_3228_);
                    v___x_3230_ = 3;
                    v___x_3231_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_3231_, 0, v___x_3229_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3231_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_3230_,
                    );
                    v___x_3232_ = lean_array_get_size(v_a_3220_);
                    v___x_3233_ = lean_array_push(v_a_3220_, v___x_3231_);
                    if v_isShared_3223_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3222_, 1);
                        leanh::lean_ctor_set(v___x_3222_, 1, v___x_3233_);
                        leanh::lean_ctor_set(v___x_3222_, 0, v___x_3232_);
                        v___x_3235_ = v___x_3222_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3236_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3232_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3233_);
                        v___x_3235_ = v_reuseFailAlloc_3236_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_3226_;
            }
            10 => {
                return v___x_3235_;
            }
            11 => {
                if v_isShared_3243_ == 0 {
                    v___x_3245_ = v___x_3242_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_a_3240_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3245_;
            }
            13 => {
                return v___x_3255_;
            }
            14 => {
                return v___x_3269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(
    mut v_pkgIdx_3287_: *mut leanh::LeanObject,
    mut v_pkgName_3288_: *mut leanh::LeanObject,
    mut v_pkgDir_3289_: *mut leanh::LeanObject,
    mut v_lakeOpts_3290_: *mut leanh::LeanObject,
    mut v_leanOpts_3291_: *mut leanh::LeanObject,
    mut v_configFile_3292_: *mut leanh::LeanObject,
    mut v_a_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(
        v_pkgIdx_3287_,
        v_pkgName_3288_,
        v_pkgDir_3289_,
        v_lakeOpts_3290_,
        v_leanOpts_3291_,
        v_configFile_3292_,
        v_a_3293_,
    );
    return v_res_3295_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(
    mut v_env_3298_: *mut leanh::LeanObject,
    mut v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_3299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3300_ = lake_environment_add(
        v_env_3298_,
        v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_3299_,
    );
    return v_res_3300_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3306_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2;
    v___x_3307_ = l_Lean_NameSet_empty;
    v___x_3308_ = l_Lean_NameSet_insert(v___x_3307_, v___x_3306_);
    return v___x_3308_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5;
    v___x_3314_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3,
    );
    v___x_3315_ = l_Lean_NameSet_insert(v___x_3314_, v___x_3313_);
    return v___x_3315_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8;
    v___x_3321_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6,
    );
    v___x_3322_ = l_Lean_NameSet_insert(v___x_3321_, v___x_3320_);
    return v___x_3322_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11;
    v___x_3328_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9,
    );
    v___x_3329_ = l_Lean_NameSet_insert(v___x_3328_, v___x_3327_);
    return v___x_3329_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3334_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14;
    v___x_3335_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12,
    );
    v___x_3336_ = l_Lean_NameSet_insert(v___x_3335_, v___x_3334_);
    return v___x_3336_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17;
    v___x_3342_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15,
    );
    v___x_3343_ = l_Lean_NameSet_insert(v___x_3342_, v___x_3341_);
    return v___x_3343_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20;
    v___x_3349_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18,
    );
    v___x_3350_ = l_Lean_NameSet_insert(v___x_3349_, v___x_3348_);
    return v___x_3350_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3355_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23;
    v___x_3356_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21,
    );
    v___x_3357_ = l_Lean_NameSet_insert(v___x_3356_, v___x_3355_);
    return v___x_3357_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26;
    v___x_3363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24,
    );
    v___x_3364_ = l_Lean_NameSet_insert(v___x_3363_, v___x_3362_);
    return v___x_3364_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3369_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29;
    v___x_3370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27,
    );
    v___x_3371_ = l_Lean_NameSet_insert(v___x_3370_, v___x_3369_);
    return v___x_3371_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3376_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32;
    v___x_3377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30,
    );
    v___x_3378_ = l_Lean_NameSet_insert(v___x_3377_, v___x_3376_);
    return v___x_3378_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35;
    v___x_3384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33,
    );
    v___x_3385_ = l_Lean_NameSet_insert(v___x_3384_, v___x_3383_);
    return v___x_3385_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38;
    v___x_3391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36,
    );
    v___x_3392_ = l_Lean_NameSet_insert(v___x_3391_, v___x_3390_);
    return v___x_3392_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41;
    v___x_3398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39,
    );
    v___x_3399_ = l_Lean_NameSet_insert(v___x_3398_, v___x_3397_);
    return v___x_3399_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44;
    v___x_3405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42,
    );
    v___x_3406_ = l_Lean_NameSet_insert(v___x_3405_, v___x_3404_);
    return v___x_3406_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49()
-> *mut leanh::LeanObject {
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3412_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48;
    v___x_3413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45,
    );
    v___x_3414_ = l_Lean_NameSet_insert(v___x_3413_, v___x_3412_);
    return v___x_3414_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53()
-> *mut leanh::LeanObject {
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52;
    v___x_3422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49,
    );
    v___x_3423_ = l_Lean_NameSet_insert(v___x_3422_, v___x_3421_);
    return v___x_3423_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts()
-> *mut leanh::LeanObject {
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once
        ),
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53,
    );
    return v___x_3424_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ = l_Lean_instInhabitedEnvExtensionState;
    v___x_3426_ = l_Lean_instInhabitedPersistentEnvExtension(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3425_,
    );
    return v___x_3426_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(
    mut v_val_3427_: *mut leanh::LeanObject,
    mut v_val_3428_: *mut leanh::LeanObject,
    mut v_as_3429_: *mut leanh::LeanObject,
    mut v_i_3430_: usize,
    mut v_stop_3431_: usize,
    mut v_b_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: usize = 0;
    let mut v___x_3441_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3433_ = lean_usize_dec_eq(v_i_3430_, v_stop_3431_);
                if v___x_3433_ == 0 {
                    v___x_3434_ = lean_array_uget_borrowed(v_as_3429_, v_i_3430_);
                    v___x_3435_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
                    v___x_3436_ = lean_array_get_borrowed(v___x_3435_, v_val_3427_, v_val_3428_);
                    v___x_3437_ = leanh::lean_box(0);
                    v___x_3438_ = leanh::lean_box(0);
                    leanh::lean_inc(v___x_3434_);
                    leanh::lean_inc(v___x_3436_);
                    v___x_3439_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                        v___x_3436_,
                        v_b_3432_,
                        v___x_3434_,
                        v___x_3437_,
                        v___x_3438_,
                    );
                    v___x_3440_ = 1usize;
                    v___x_3441_ = lean_usize_add(v_i_3430_, v___x_3440_);
                    v_i_3430_ = v___x_3441_;
                    v_b_3432_ = v___x_3439_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3432_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(
    mut v_val_3443_: *mut leanh::LeanObject,
    mut v_val_3444_: *mut leanh::LeanObject,
    mut v_as_3445_: *mut leanh::LeanObject,
    mut v_i_3446_: *mut leanh::LeanObject,
    mut v_stop_3447_: *mut leanh::LeanObject,
    mut v_b_3448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3449_: usize = 0;
    let mut v_stop_boxed_3450_: usize = 0;
    let mut v_res_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3449_ = leanh::lean_unbox_usize(v_i_3446_);
    leanh::lean_dec(v_i_3446_);
    v_stop_boxed_3450_ = leanh::lean_unbox_usize(v_stop_3447_);
    leanh::lean_dec(v_stop_3447_);
    v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_3443_, v_val_3444_, v_as_3445_, v_i_boxed_3449_, v_stop_boxed_3450_, v_b_3448_);
    leanh::lean_dec_ref(v_as_3445_);
    leanh::lean_dec(v_val_3444_);
    leanh::lean_dec_ref(v_val_3443_);
    return v_res_3451_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(
    mut v_a_3452_: *mut leanh::LeanObject,
    mut v_x_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3453_) == 0 {
                    v___x_3454_ = leanh::lean_box(0);
                    return v___x_3454_;
                } else {
                    v_key_3455_ = leanh::lean_ctor_get(v_x_3453_, 0);
                    v_value_3456_ = leanh::lean_ctor_get(v_x_3453_, 1);
                    v_tail_3457_ = leanh::lean_ctor_get(v_x_3453_, 2);
                    v___x_3458_ = lean_name_eq(v_key_3455_, v_a_3452_);
                    if v___x_3458_ == 0 {
                        v_x_3453_ = v_tail_3457_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3456_);
                        v___x_3460_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3460_, 0, v_value_3456_);
                        return v___x_3460_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(
    mut v_a_3461_: *mut leanh::LeanObject,
    mut v_x_3462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_3461_, v_x_3462_);
    leanh::lean_dec(v_x_3462_);
    leanh::lean_dec(v_a_3461_);
    return v_res_3463_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u64 = 0;
    v___x_3464_ = leanh::lean_unsigned_to_nat(1723);
    v___x_3465_ = lean_uint64_of_nat(v___x_3464_);
    return v___x_3465_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(
    mut v_m_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3471_: u64 = 0;
    let mut v___x_3472_: u64 = 0;
    let mut v___x_3473_: u64 = 0;
    let mut v_fold_3474_: u64 = 0;
    let mut v___x_3475_: u64 = 0;
    let mut v___x_3476_: u64 = 0;
    let mut v___x_3477_: u64 = 0;
    let mut v___x_3478_: usize = 0;
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    let mut v___x_3481_: usize = 0;
    let mut v___x_3482_: usize = 0;
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: u64 = 0;
    let mut v_hash_3486_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3468_ = leanh::lean_ctor_get(v_m_3466_, 1);
                v___x_3469_ = lean_array_get_size(v_buckets_3468_);
                if leanh::lean_obj_tag(v_a_3467_) == 0 {
                    v___x_3485_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0);
                    v___y_3471_ = v___x_3485_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3486_ = leanh::lean_ctor_get_uint64(
                        v_a_3467_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3471_ = v_hash_3486_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3472_ = 32u64;
                v___x_3473_ = lean_uint64_shift_right(v___y_3471_, v___x_3472_);
                v_fold_3474_ = lean_uint64_xor(v___y_3471_, v___x_3473_);
                v___x_3475_ = 16u64;
                v___x_3476_ = lean_uint64_shift_right(v_fold_3474_, v___x_3475_);
                v___x_3477_ = lean_uint64_xor(v_fold_3474_, v___x_3476_);
                v___x_3478_ = lean_uint64_to_usize(v___x_3477_);
                v___x_3479_ = lean_usize_of_nat(v___x_3469_);
                v___x_3480_ = 1usize;
                v___x_3481_ = lean_usize_sub(v___x_3479_, v___x_3480_);
                v___x_3482_ = lean_usize_land(v___x_3478_, v___x_3481_);
                v___x_3483_ = lean_array_uget_borrowed(v_buckets_3468_, v___x_3482_);
                v___x_3484_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_3467_, v___x_3483_);
                return v___x_3484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(
    mut v_m_3487_: *mut leanh::LeanObject,
    mut v_a_3488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_3487_, v_a_3488_);
    leanh::lean_dec(v_a_3488_);
    leanh::lean_dec_ref(v_m_3487_);
    return v_res_3489_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(
    mut v_a_3490_: *mut leanh::LeanObject,
    mut v_val_3491_: *mut leanh::LeanObject,
    mut v_as_3492_: *mut leanh::LeanObject,
    mut v_i_3493_: usize,
    mut v_stop_3494_: usize,
    mut v_b_3495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: usize = 0;
    let mut v___x_3499_: usize = 0;
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: u8 = 0;
    let mut v___x_3513_: usize = 0;
    let mut v___x_3514_: usize = 0;
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: usize = 0;
    let mut v___x_3517_: usize = 0;
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3501_ = lean_usize_dec_eq(v_i_3493_, v_stop_3494_);
                if v___x_3501_ == 0 {
                    v___x_3502_ = lean_array_uget_borrowed(v_as_3492_, v_i_3493_);
                    v_fst_3503_ = leanh::lean_ctor_get(v___x_3502_, 0);
                    v_snd_3504_ = leanh::lean_ctor_get(v___x_3502_, 1);
                    v___x_3505_ =
                        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
                    v___x_3506_ = l_Lean_NameSet_contains(v___x_3505_, v_fst_3503_);
                    if v___x_3506_ == 0 {
                        v___y_3497_ = v_b_3495_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_3490_, v_fst_3503_);
                        if leanh::lean_obj_tag(v___x_3507_) == 0 {
                            v___y_3497_ = v_b_3495_;
                            state = 1;
                            continue;
                        } else {
                            v_val_3508_ = leanh::lean_ctor_get(v___x_3507_, 0);
                            leanh::lean_inc(v_val_3508_);
                            leanh::lean_dec_ref_known(v___x_3507_, 1);
                            v___x_3509_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3510_ = lean_array_get_size(v_snd_3504_);
                            v___x_3511_ = lean_nat_dec_lt(v___x_3509_, v___x_3510_);
                            if v___x_3511_ == 0 {
                                leanh::lean_dec(v_val_3508_);
                                v___y_3497_ = v_b_3495_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3512_ = lean_nat_dec_le(v___x_3510_, v___x_3510_);
                                if v___x_3512_ == 0 {
                                    if v___x_3511_ == 0 {
                                        leanh::lean_dec(v_val_3508_);
                                        v___y_3497_ = v_b_3495_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3513_ = 0usize;
                                        v___x_3514_ = lean_usize_of_nat(v___x_3510_);
                                        v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_3491_, v_val_3508_, v_snd_3504_, v___x_3513_, v___x_3514_, v_b_3495_);
                                        leanh::lean_dec(v_val_3508_);
                                        v___y_3497_ = v___x_3515_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_3516_ = 0usize;
                                    v___x_3517_ = lean_usize_of_nat(v___x_3510_);
                                    v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_3491_, v_val_3508_, v_snd_3504_, v___x_3516_, v___x_3517_, v_b_3495_);
                                    leanh::lean_dec(v_val_3508_);
                                    v___y_3497_ = v___x_3518_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    return v_b_3495_;
                }
            }
            1 => {
                v___x_3498_ = 1usize;
                v___x_3499_ = lean_usize_add(v_i_3493_, v___x_3498_);
                v_i_3493_ = v___x_3499_;
                v_b_3495_ = v___y_3497_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(
    mut v_a_3519_: *mut leanh::LeanObject,
    mut v_val_3520_: *mut leanh::LeanObject,
    mut v_as_3521_: *mut leanh::LeanObject,
    mut v_i_3522_: *mut leanh::LeanObject,
    mut v_stop_3523_: *mut leanh::LeanObject,
    mut v_b_3524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3525_: usize = 0;
    let mut v_stop_boxed_3526_: usize = 0;
    let mut v_res_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3525_ = leanh::lean_unbox_usize(v_i_3522_);
    leanh::lean_dec(v_i_3522_);
    v_stop_boxed_3526_ = leanh::lean_unbox_usize(v_stop_3523_);
    leanh::lean_dec(v_stop_3523_);
    v_res_3527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_3519_, v_val_3520_, v_as_3521_, v_i_boxed_3525_, v_stop_boxed_3526_, v_b_3524_);
    leanh::lean_dec_ref(v_as_3521_);
    leanh::lean_dec_ref(v_val_3520_);
    leanh::lean_dec_ref(v_a_3519_);
    return v_res_3527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(
    mut v_as_3528_: *mut leanh::LeanObject,
    mut v_i_3529_: usize,
    mut v_stop_3530_: usize,
    mut v_b_3531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: usize = 0;
    let mut v___x_3536_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3532_ = lean_usize_dec_eq(v_i_3529_, v_stop_3530_);
                if v___x_3532_ == 0 {
                    v___x_3533_ = lean_array_uget_borrowed(v_as_3528_, v_i_3529_);
                    leanh::lean_inc(v___x_3533_);
                    v___x_3534_ = lake_environment_add(v_b_3531_, v___x_3533_);
                    v___x_3535_ = 1usize;
                    v___x_3536_ = lean_usize_add(v_i_3529_, v___x_3535_);
                    v_i_3529_ = v___x_3536_;
                    v_b_3531_ = v___x_3534_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3531_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(
    mut v_as_3538_: *mut leanh::LeanObject,
    mut v_i_3539_: *mut leanh::LeanObject,
    mut v_stop_3540_: *mut leanh::LeanObject,
    mut v_b_3541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3542_: usize = 0;
    let mut v_stop_boxed_3543_: usize = 0;
    let mut v_res_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3542_ = leanh::lean_unbox_usize(v_i_3539_);
    leanh::lean_dec(v_i_3539_);
    v_stop_boxed_3543_ = leanh::lean_unbox_usize(v_stop_3540_);
    leanh::lean_dec(v_stop_3540_);
    v_res_3544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_3538_, v_i_boxed_3542_, v_stop_boxed_3543_, v_b_3541_);
    leanh::lean_dec_ref(v_as_3538_);
    return v_res_3544_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(
    mut v_olean_3545_: *mut leanh::LeanObject,
    mut v_leanOpts_3546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_constants_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: u32 = 0;
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: usize = 0;
    let mut v___x_3577_: usize = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: usize = 0;
    let mut v___x_3583_: usize = 0;
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_a_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: u8 = 0;
    let mut v___x_3600_: usize = 0;
    let mut v___x_3601_: usize = 0;
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: usize = 0;
    let mut v___x_3604_: usize = 0;
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3609_: u8 = 0;
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3548_ = l_Lean_readModuleData(v_olean_3545_);
                if leanh::lean_obj_tag(v___x_3548_) == 0 {
                    v_a_3549_ = leanh::lean_ctor_get(v___x_3548_, 0);
                    leanh::lean_inc(v_a_3549_);
                    leanh::lean_dec_ref_known(v___x_3548_, 1);
                    v_fst_3550_ = leanh::lean_ctor_get(v_a_3549_, 0);
                    leanh::lean_inc(v_fst_3550_);
                    leanh::lean_dec(v_a_3549_);
                    v_imports_3551_ = leanh::lean_ctor_get(v_fst_3550_, 0);
                    leanh::lean_inc_ref(v_imports_3551_);
                    v_constants_3552_ = leanh::lean_ctor_get(v_fst_3550_, 2);
                    leanh::lean_inc_ref(v_constants_3552_);
                    v_entries_3553_ = leanh::lean_ctor_get(v_fst_3550_, 4);
                    leanh::lean_inc_ref(v_entries_3553_);
                    leanh::lean_dec(v_fst_3550_);
                    v___x_3554_ = 1024;
                    v___x_3555_ = l_Lake_importModulesUsingCache(
                        v_imports_3551_,
                        v_leanOpts_3546_,
                        v___x_3554_,
                    );
                    if leanh::lean_obj_tag(v___x_3555_) == 0 {
                        v_a_3556_ = leanh::lean_ctor_get(v___x_3555_, 0);
                        leanh::lean_inc(v_a_3556_);
                        leanh::lean_dec_ref_known(v___x_3555_, 1);
                        v___x_3557_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3597_ = lean_array_get_size(v_constants_3552_);
                        v___x_3598_ = lean_nat_dec_lt(v___x_3557_, v___x_3597_);
                        if v___x_3598_ == 0 {
                            leanh::lean_dec_ref(v_constants_3552_);
                            v___y_3559_ = v_a_3556_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3599_ = lean_nat_dec_le(v___x_3597_, v___x_3597_);
                            if v___x_3599_ == 0 {
                                if v___x_3598_ == 0 {
                                    leanh::lean_dec_ref(v_constants_3552_);
                                    v___y_3559_ = v_a_3556_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3600_ = 0usize;
                                    v___x_3601_ = lean_usize_of_nat(v___x_3597_);
                                    v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_3552_, v___x_3600_, v___x_3601_, v_a_3556_);
                                    leanh::lean_dec_ref(v_constants_3552_);
                                    v___y_3559_ = v___x_3602_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_3603_ = 0usize;
                                v___x_3604_ = lean_usize_of_nat(v___x_3597_);
                                v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_3552_, v___x_3603_, v___x_3604_, v_a_3556_);
                                leanh::lean_dec_ref(v_constants_3552_);
                                v___y_3559_ = v___x_3605_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_entries_3553_);
                        leanh::lean_dec_ref(v_constants_3552_);
                        return v___x_3555_;
                    }
                } else {
                    leanh::lean_dec_ref(v_leanOpts_3546_);
                    v_a_3606_ = leanh::lean_ctor_get(v___x_3548_, 0);
                    v_isSharedCheck_3613_ = (!leanh::lean_is_exclusive(v___x_3548_)) as u8;
                    if v_isSharedCheck_3613_ == 0 {
                        v___x_3608_ = v___x_3548_;
                        v_isShared_3609_ = v_isSharedCheck_3613_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3606_);
                        leanh::lean_dec(v___x_3548_);
                        v___x_3608_ = leanh::lean_box(0);
                        v_isShared_3609_ = v_isSharedCheck_3613_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3560_ = l_Lean_persistentEnvExtensionsRef;
                v___x_3561_ = lean_st_ref_get(v___x_3560_);
                v___x_3562_ = l_Lean_mkExtNameMap(v___x_3557_);
                if leanh::lean_obj_tag(v___x_3562_) == 0 {
                    v_a_3563_ = leanh::lean_ctor_get(v___x_3562_, 0);
                    v_isSharedCheck_3588_ = (!leanh::lean_is_exclusive(v___x_3562_)) as u8;
                    if v_isSharedCheck_3588_ == 0 {
                        v___x_3565_ = v___x_3562_;
                        v_isShared_3566_ = v_isSharedCheck_3588_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3563_);
                        leanh::lean_dec(v___x_3562_);
                        v___x_3565_ = leanh::lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3588_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3561_);
                    leanh::lean_dec_ref(v___y_3559_);
                    leanh::lean_dec_ref(v_entries_3553_);
                    v_a_3589_ = leanh::lean_ctor_get(v___x_3562_, 0);
                    v_isSharedCheck_3596_ = (!leanh::lean_is_exclusive(v___x_3562_)) as u8;
                    if v_isSharedCheck_3596_ == 0 {
                        v___x_3591_ = v___x_3562_;
                        v_isShared_3592_ = v_isSharedCheck_3596_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3589_);
                        leanh::lean_dec(v___x_3562_);
                        v___x_3591_ = leanh::lean_box(0);
                        v_isShared_3592_ = v_isSharedCheck_3596_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3567_ = lean_array_get_size(v_entries_3553_);
                v___x_3568_ = lean_nat_dec_lt(v___x_3557_, v___x_3567_);
                if v___x_3568_ == 0 {
                    leanh::lean_dec(v_a_3563_);
                    leanh::lean_dec(v___x_3561_);
                    leanh::lean_dec_ref(v_entries_3553_);
                    if v_isShared_3566_ == 0 {
                        leanh::lean_ctor_set(v___x_3565_, 0, v___y_3559_);
                        v___x_3570_ = v___x_3565_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___y_3559_);
                        v___x_3570_ = v_reuseFailAlloc_3571_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3572_ = lean_nat_dec_le(v___x_3567_, v___x_3567_);
                    if v___x_3572_ == 0 {
                        if v___x_3568_ == 0 {
                            leanh::lean_dec(v_a_3563_);
                            leanh::lean_dec(v___x_3561_);
                            leanh::lean_dec_ref(v_entries_3553_);
                            if v_isShared_3566_ == 0 {
                                leanh::lean_ctor_set(v___x_3565_, 0, v___y_3559_);
                                v___x_3574_ = v___x_3565_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3575_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___y_3559_);
                                v___x_3574_ = v_reuseFailAlloc_3575_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_3576_ = 0usize;
                            v___x_3577_ = lean_usize_of_nat(v___x_3567_);
                            v___x_3578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_3563_, v___x_3561_, v_entries_3553_, v___x_3576_, v___x_3577_, v___y_3559_);
                            leanh::lean_dec_ref(v_entries_3553_);
                            leanh::lean_dec(v___x_3561_);
                            leanh::lean_dec(v_a_3563_);
                            if v_isShared_3566_ == 0 {
                                leanh::lean_ctor_set(v___x_3565_, 0, v___x_3578_);
                                v___x_3580_ = v___x_3565_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_3581_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
                                v___x_3580_ = v_reuseFailAlloc_3581_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_3582_ = 0usize;
                        v___x_3583_ = lean_usize_of_nat(v___x_3567_);
                        v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_3563_, v___x_3561_, v_entries_3553_, v___x_3582_, v___x_3583_, v___y_3559_);
                        leanh::lean_dec_ref(v_entries_3553_);
                        leanh::lean_dec(v___x_3561_);
                        leanh::lean_dec(v_a_3563_);
                        if v_isShared_3566_ == 0 {
                            leanh::lean_ctor_set(v___x_3565_, 0, v___x_3584_);
                            v___x_3586_ = v___x_3565_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3587_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
                            v___x_3586_ = v_reuseFailAlloc_3587_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3570_;
            }
            4 => {
                return v___x_3574_;
            }
            5 => {
                return v___x_3580_;
            }
            6 => {
                return v___x_3586_;
            }
            7 => {
                if v_isShared_3592_ == 0 {
                    v___x_3594_ = v___x_3591_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3595_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
                    v___x_3594_ = v_reuseFailAlloc_3595_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3594_;
            }
            9 => {
                if v_isShared_3609_ == 0 {
                    v___x_3611_ = v___x_3608_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
                    v___x_3611_ = v_reuseFailAlloc_3612_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(
    mut v_olean_3614_: *mut leanh::LeanObject,
    mut v_leanOpts_3615_: *mut leanh::LeanObject,
    mut v_a_3616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3617_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(
        v_olean_3614_,
        v_leanOpts_3615_,
    );
    leanh::lean_dec_ref(v_olean_3614_);
    return v_res_3617_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(
    mut v_00_u03b2_3618_: *mut leanh::LeanObject,
    mut v_m_3619_: *mut leanh::LeanObject,
    mut v_a_3620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_3619_, v_a_3620_);
    return v___x_3621_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(
    mut v_00_u03b2_3622_: *mut leanh::LeanObject,
    mut v_m_3623_: *mut leanh::LeanObject,
    mut v_a_3624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_3622_, v_m_3623_, v_a_3624_);
    leanh::lean_dec(v_a_3624_);
    leanh::lean_dec_ref(v_m_3623_);
    return v_res_3625_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(
    mut v_00_u03b2_3626_: *mut leanh::LeanObject,
    mut v_a_3627_: *mut leanh::LeanObject,
    mut v_x_3628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3629_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_3627_, v_x_3628_);
    return v___x_3629_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(
    mut v_00_u03b2_3630_: *mut leanh::LeanObject,
    mut v_a_3631_: *mut leanh::LeanObject,
    mut v_x_3632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3633_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_3630_, v_a_3631_, v_x_3632_);
    leanh::lean_dec(v_x_3632_);
    leanh::lean_dec(v_a_3631_);
    return v_res_3633_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(
    mut v_msg_3634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3635_ = leanh::lean_box(1);
    v___x_3636_ = lean_panic_fn_borrowed(v___x_3635_, v_msg_3634_);
    return v___x_3636_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3640_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2;
    v___x_3641_ = leanh::lean_unsigned_to_nat(35);
    v___x_3642_ = leanh::lean_unsigned_to_nat(182);
    v___x_3643_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1;
    v___x_3644_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_3645_ = l_mkPanicMessageWithDecl(
        v___x_3644_,
        v___x_3643_,
        v___x_3642_,
        v___x_3641_,
        v___x_3640_,
    );
    return v___x_3645_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2;
    v___x_3647_ = leanh::lean_unsigned_to_nat(21);
    v___x_3648_ = leanh::lean_unsigned_to_nat(183);
    v___x_3649_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1;
    v___x_3650_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_3651_ = l_mkPanicMessageWithDecl(
        v___x_3650_,
        v___x_3649_,
        v___x_3648_,
        v___x_3647_,
        v___x_3646_,
    );
    return v___x_3651_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3654_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6;
    v___x_3655_ = leanh::lean_unsigned_to_nat(35);
    v___x_3656_ = leanh::lean_unsigned_to_nat(276);
    v___x_3657_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5;
    v___x_3658_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_3659_ = l_mkPanicMessageWithDecl(
        v___x_3658_,
        v___x_3657_,
        v___x_3656_,
        v___x_3655_,
        v___x_3654_,
    );
    return v___x_3659_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3660_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6;
    v___x_3661_ = leanh::lean_unsigned_to_nat(21);
    v___x_3662_ = leanh::lean_unsigned_to_nat(277);
    v___x_3663_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5;
    v___x_3664_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_3665_ = l_mkPanicMessageWithDecl(
        v___x_3664_,
        v___x_3663_,
        v___x_3662_,
        v___x_3661_,
        v___x_3660_,
    );
    return v___x_3665_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(
    mut v_k_3666_: *mut leanh::LeanObject,
    mut v_v_3667_: *mut leanh::LeanObject,
    mut v_t_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3677_: u8 = 0;
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: u8 = 0;
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v_size_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: u8 = 0;
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_unused_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3750_: u8 = 0;
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v_unused_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_unused_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3784_: u8 = 0;
    let mut v_size_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_unused_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3811_: u8 = 0;
    let mut v_unused_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3820_: u8 = 0;
    let mut v_k_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_unused_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut v_unused_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3874_: u8 = 0;
    let mut v_size_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut v_unused_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3926_: u8 = 0;
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut v_unused_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3941_: u8 = 0;
    let mut v_unused_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3960_: u8 = 0;
    let mut v_size_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut v_unused_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3978_: u8 = 0;
    let mut v_k_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_unused_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3999_: u8 = 0;
    let mut v_unused_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4017_: u8 = 0;
    let mut v_unused_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3668_) == 0 {
                    v_size_3669_ = leanh::lean_ctor_get(v_t_3668_, 0);
                    v_k_3670_ = leanh::lean_ctor_get(v_t_3668_, 1);
                    v_v_3671_ = leanh::lean_ctor_get(v_t_3668_, 2);
                    v_l_3672_ = leanh::lean_ctor_get(v_t_3668_, 3);
                    v_r_3673_ = leanh::lean_ctor_get(v_t_3668_, 4);
                    v_isSharedCheck_4029_ = (!leanh::lean_is_exclusive(v_t_3668_)) as u8;
                    if v_isSharedCheck_4029_ == 0 {
                        v___x_3675_ = v_t_3668_;
                        v_isShared_3676_ = v_isSharedCheck_4029_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_3673_);
                        leanh::lean_inc(v_l_3672_);
                        leanh::lean_inc(v_v_3671_);
                        leanh::lean_inc(v_k_3670_);
                        leanh::lean_inc(v_size_3669_);
                        leanh::lean_dec(v_t_3668_);
                        v___x_3675_ = leanh::lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_4029_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4030_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4031_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_4031_, 0, v___x_4030_);
                    leanh::lean_ctor_set(v___x_4031_, 1, v_k_3666_);
                    leanh::lean_ctor_set(v___x_4031_, 2, v_v_3667_);
                    leanh::lean_ctor_set(v___x_4031_, 3, v_t_3668_);
                    leanh::lean_ctor_set(v___x_4031_, 4, v_t_3668_);
                    return v___x_4031_;
                }
            }
            1 => {
                v___x_3677_ = lean_string_compare(v_k_3666_, v_k_3670_);
                match v___x_3677_ {
                    0 => {
                        leanh::lean_dec(v_size_3669_);
                        v___x_3678_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_3666_, v_v_3667_, v_l_3672_);
                        if leanh::lean_obj_tag(v_r_3673_) == 0 {
                            if leanh::lean_obj_tag(v___x_3678_) == 0 {
                                v_size_3679_ = leanh::lean_ctor_get(v_r_3673_, 0);
                                v_size_3680_ = leanh::lean_ctor_get(v___x_3678_, 0);
                                leanh::lean_inc(v_size_3680_);
                                v_k_3681_ = leanh::lean_ctor_get(v___x_3678_, 1);
                                leanh::lean_inc(v_k_3681_);
                                v_v_3682_ = leanh::lean_ctor_get(v___x_3678_, 2);
                                leanh::lean_inc(v_v_3682_);
                                v_l_3683_ = leanh::lean_ctor_get(v___x_3678_, 3);
                                leanh::lean_inc(v_l_3683_);
                                v_r_3684_ = leanh::lean_ctor_get(v___x_3678_, 4);
                                leanh::lean_inc(v_r_3684_);
                                v___x_3685_ = leanh::lean_unsigned_to_nat(3);
                                v___x_3686_ = lean_nat_mul(v___x_3685_, v_size_3679_);
                                v___x_3687_ = lean_nat_dec_lt(v___x_3686_, v_size_3680_);
                                leanh::lean_dec(v___x_3686_);
                                if v___x_3687_ == 0 {
                                    leanh::lean_dec(v_r_3684_);
                                    leanh::lean_dec(v_l_3683_);
                                    leanh::lean_dec(v_v_3682_);
                                    leanh::lean_dec(v_k_3681_);
                                    v___x_3688_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_3689_ = lean_nat_add(v___x_3688_, v_size_3680_);
                                    leanh::lean_dec(v_size_3680_);
                                    v___x_3690_ = lean_nat_add(v___x_3689_, v_size_3679_);
                                    leanh::lean_dec(v___x_3689_);
                                    if v_isShared_3676_ == 0 {
                                        leanh::lean_ctor_set(v___x_3675_, 3, v___x_3678_);
                                        leanh::lean_ctor_set(v___x_3675_, 0, v___x_3690_);
                                        v___x_3692_ = v___x_3675_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3693_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3693_,
                                            0,
                                            v___x_3690_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3693_,
                                            1,
                                            v_k_3670_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3693_,
                                            2,
                                            v_v_3671_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3693_,
                                            3,
                                            v___x_3678_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3693_,
                                            4,
                                            v_r_3673_,
                                        );
                                        v___x_3692_ = v_reuseFailAlloc_3693_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3765_ =
                                        (!leanh::lean_is_exclusive(v___x_3678_)) as u8;
                                    if v_isSharedCheck_3765_ == 0 {
                                        v_unused_3766_ =
                                            leanh::lean_ctor_get(v___x_3678_, 4);
                                        leanh::lean_dec(v_unused_3766_);
                                        v_unused_3767_ =
                                            leanh::lean_ctor_get(v___x_3678_, 3);
                                        leanh::lean_dec(v_unused_3767_);
                                        v_unused_3768_ =
                                            leanh::lean_ctor_get(v___x_3678_, 2);
                                        leanh::lean_dec(v_unused_3768_);
                                        v_unused_3769_ =
                                            leanh::lean_ctor_get(v___x_3678_, 1);
                                        leanh::lean_dec(v_unused_3769_);
                                        v_unused_3770_ =
                                            leanh::lean_ctor_get(v___x_3678_, 0);
                                        leanh::lean_dec(v_unused_3770_);
                                        v___x_3695_ = v___x_3678_;
                                        v_isShared_3696_ = v_isSharedCheck_3765_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3678_);
                                        v___x_3695_ = leanh::lean_box(0);
                                        v_isShared_3696_ = v_isSharedCheck_3765_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3771_ = leanh::lean_ctor_get(v_r_3673_, 0);
                                v___x_3772_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3773_ = lean_nat_add(v___x_3772_, v_size_3771_);
                                if v_isShared_3676_ == 0 {
                                    leanh::lean_ctor_set(v___x_3675_, 3, v___x_3678_);
                                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3773_);
                                    v___x_3775_ = v___x_3675_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3776_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3776_,
                                        0,
                                        v___x_3773_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3776_,
                                        1,
                                        v_k_3670_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3776_,
                                        2,
                                        v_v_3671_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3776_,
                                        3,
                                        v___x_3678_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3776_,
                                        4,
                                        v_r_3673_,
                                    );
                                    v___x_3775_ = v_reuseFailAlloc_3776_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_3678_) == 0 {
                                v_l_3777_ = leanh::lean_ctor_get(v___x_3678_, 3);
                                leanh::lean_inc(v_l_3777_);
                                if leanh::lean_obj_tag(v_l_3777_) == 0 {
                                    v_r_3778_ = leanh::lean_ctor_get(v___x_3678_, 4);
                                    leanh::lean_inc(v_r_3778_);
                                    if leanh::lean_obj_tag(v_r_3778_) == 0 {
                                        v_size_3779_ = leanh::lean_ctor_get(v___x_3678_, 0);
                                        v_k_3780_ = leanh::lean_ctor_get(v___x_3678_, 1);
                                        v_v_3781_ = leanh::lean_ctor_get(v___x_3678_, 2);
                                        v_isSharedCheck_3795_ =
                                            (!leanh::lean_is_exclusive(v___x_3678_)) as u8;
                                        if v_isSharedCheck_3795_ == 0 {
                                            v_unused_3796_ =
                                                leanh::lean_ctor_get(v___x_3678_, 4);
                                            leanh::lean_dec(v_unused_3796_);
                                            v_unused_3797_ =
                                                leanh::lean_ctor_get(v___x_3678_, 3);
                                            leanh::lean_dec(v_unused_3797_);
                                            v___x_3783_ = v___x_3678_;
                                            v_isShared_3784_ = v_isSharedCheck_3795_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3781_);
                                            leanh::lean_inc(v_k_3780_);
                                            leanh::lean_inc(v_size_3779_);
                                            leanh::lean_dec(v___x_3678_);
                                            v___x_3783_ = leanh::lean_box(0);
                                            v_isShared_3784_ = v_isSharedCheck_3795_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_3798_ = leanh::lean_ctor_get(v___x_3678_, 1);
                                        v_v_3799_ = leanh::lean_ctor_get(v___x_3678_, 2);
                                        v_isSharedCheck_3811_ =
                                            (!leanh::lean_is_exclusive(v___x_3678_)) as u8;
                                        if v_isSharedCheck_3811_ == 0 {
                                            v_unused_3812_ =
                                                leanh::lean_ctor_get(v___x_3678_, 4);
                                            leanh::lean_dec(v_unused_3812_);
                                            v_unused_3813_ =
                                                leanh::lean_ctor_get(v___x_3678_, 3);
                                            leanh::lean_dec(v_unused_3813_);
                                            v_unused_3814_ =
                                                leanh::lean_ctor_get(v___x_3678_, 0);
                                            leanh::lean_dec(v_unused_3814_);
                                            v___x_3801_ = v___x_3678_;
                                            v_isShared_3802_ = v_isSharedCheck_3811_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3799_);
                                            leanh::lean_inc(v_k_3798_);
                                            leanh::lean_dec(v___x_3678_);
                                            v___x_3801_ = leanh::lean_box(0);
                                            v_isShared_3802_ = v_isSharedCheck_3811_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3815_ = leanh::lean_ctor_get(v___x_3678_, 4);
                                    leanh::lean_inc(v_r_3815_);
                                    if leanh::lean_obj_tag(v_r_3815_) == 0 {
                                        v_k_3816_ = leanh::lean_ctor_get(v___x_3678_, 1);
                                        v_v_3817_ = leanh::lean_ctor_get(v___x_3678_, 2);
                                        v_isSharedCheck_3841_ =
                                            (!leanh::lean_is_exclusive(v___x_3678_)) as u8;
                                        if v_isSharedCheck_3841_ == 0 {
                                            v_unused_3842_ =
                                                leanh::lean_ctor_get(v___x_3678_, 4);
                                            leanh::lean_dec(v_unused_3842_);
                                            v_unused_3843_ =
                                                leanh::lean_ctor_get(v___x_3678_, 3);
                                            leanh::lean_dec(v_unused_3843_);
                                            v_unused_3844_ =
                                                leanh::lean_ctor_get(v___x_3678_, 0);
                                            leanh::lean_dec(v_unused_3844_);
                                            v___x_3819_ = v___x_3678_;
                                            v_isShared_3820_ = v_isSharedCheck_3841_;
                                            state = 20;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3817_);
                                            leanh::lean_inc(v_k_3816_);
                                            leanh::lean_dec(v___x_3678_);
                                            v___x_3819_ = leanh::lean_box(0);
                                            v_isShared_3820_ = v_isSharedCheck_3841_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_3845_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3676_ == 0 {
                                            leanh::lean_ctor_set(v___x_3675_, 4, v_r_3815_);
                                            leanh::lean_ctor_set(
                                                v___x_3675_,
                                                3,
                                                v___x_3678_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3675_,
                                                0,
                                                v___x_3845_,
                                            );
                                            v___x_3847_ = v___x_3675_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3848_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3848_,
                                                0,
                                                v___x_3845_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3848_,
                                                1,
                                                v_k_3670_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3848_,
                                                2,
                                                v_v_3671_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3848_,
                                                3,
                                                v___x_3678_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3848_,
                                                4,
                                                v_r_3815_,
                                            );
                                            v___x_3847_ = v_reuseFailAlloc_3848_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3849_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_3676_ == 0 {
                                    leanh::lean_ctor_set(v___x_3675_, 4, v___x_3678_);
                                    leanh::lean_ctor_set(v___x_3675_, 3, v___x_3678_);
                                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3849_);
                                    v___x_3851_ = v___x_3675_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3852_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3852_,
                                        0,
                                        v___x_3849_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3852_,
                                        1,
                                        v_k_3670_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3852_,
                                        2,
                                        v_v_3671_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3852_,
                                        3,
                                        v___x_3678_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3852_,
                                        4,
                                        v___x_3678_,
                                    );
                                    v___x_3851_ = v_reuseFailAlloc_3852_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_3671_);
                        leanh::lean_dec(v_k_3670_);
                        if v_isShared_3676_ == 0 {
                            leanh::lean_ctor_set(v___x_3675_, 2, v_v_3667_);
                            leanh::lean_ctor_set(v___x_3675_, 1, v_k_3666_);
                            v___x_3854_ = v___x_3675_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_3855_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_size_3669_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3666_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3667_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 3, v_l_3672_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 4, v_r_3673_);
                            v___x_3854_ = v_reuseFailAlloc_3855_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_3669_);
                        v___x_3856_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_3666_, v_v_3667_, v_r_3673_);
                        if leanh::lean_obj_tag(v_l_3672_) == 0 {
                            if leanh::lean_obj_tag(v___x_3856_) == 0 {
                                v_size_3857_ = leanh::lean_ctor_get(v_l_3672_, 0);
                                v_size_3858_ = leanh::lean_ctor_get(v___x_3856_, 0);
                                leanh::lean_inc(v_size_3858_);
                                v_k_3859_ = leanh::lean_ctor_get(v___x_3856_, 1);
                                leanh::lean_inc(v_k_3859_);
                                v_v_3860_ = leanh::lean_ctor_get(v___x_3856_, 2);
                                leanh::lean_inc(v_v_3860_);
                                v_l_3861_ = leanh::lean_ctor_get(v___x_3856_, 3);
                                leanh::lean_inc(v_l_3861_);
                                v_r_3862_ = leanh::lean_ctor_get(v___x_3856_, 4);
                                leanh::lean_inc(v_r_3862_);
                                v___x_3863_ = leanh::lean_unsigned_to_nat(3);
                                v___x_3864_ = lean_nat_mul(v___x_3863_, v_size_3857_);
                                v___x_3865_ = lean_nat_dec_lt(v___x_3864_, v_size_3858_);
                                leanh::lean_dec(v___x_3864_);
                                if v___x_3865_ == 0 {
                                    leanh::lean_dec(v_r_3862_);
                                    leanh::lean_dec(v_l_3861_);
                                    leanh::lean_dec(v_v_3860_);
                                    leanh::lean_dec(v_k_3859_);
                                    v___x_3866_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_3867_ = lean_nat_add(v___x_3866_, v_size_3857_);
                                    v___x_3868_ = lean_nat_add(v___x_3867_, v_size_3858_);
                                    leanh::lean_dec(v_size_3858_);
                                    leanh::lean_dec(v___x_3867_);
                                    if v_isShared_3676_ == 0 {
                                        leanh::lean_ctor_set(v___x_3675_, 4, v___x_3856_);
                                        leanh::lean_ctor_set(v___x_3675_, 0, v___x_3868_);
                                        v___x_3870_ = v___x_3675_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3871_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3871_,
                                            0,
                                            v___x_3868_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3871_,
                                            1,
                                            v_k_3670_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3871_,
                                            2,
                                            v_v_3671_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3871_,
                                            3,
                                            v_l_3672_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3871_,
                                            4,
                                            v___x_3856_,
                                        );
                                        v___x_3870_ = v_reuseFailAlloc_3871_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3941_ =
                                        (!leanh::lean_is_exclusive(v___x_3856_)) as u8;
                                    if v_isSharedCheck_3941_ == 0 {
                                        v_unused_3942_ =
                                            leanh::lean_ctor_get(v___x_3856_, 4);
                                        leanh::lean_dec(v_unused_3942_);
                                        v_unused_3943_ =
                                            leanh::lean_ctor_get(v___x_3856_, 3);
                                        leanh::lean_dec(v_unused_3943_);
                                        v_unused_3944_ =
                                            leanh::lean_ctor_get(v___x_3856_, 2);
                                        leanh::lean_dec(v_unused_3944_);
                                        v_unused_3945_ =
                                            leanh::lean_ctor_get(v___x_3856_, 1);
                                        leanh::lean_dec(v_unused_3945_);
                                        v_unused_3946_ =
                                            leanh::lean_ctor_get(v___x_3856_, 0);
                                        leanh::lean_dec(v_unused_3946_);
                                        v___x_3873_ = v___x_3856_;
                                        v_isShared_3874_ = v_isSharedCheck_3941_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3856_);
                                        v___x_3873_ = leanh::lean_box(0);
                                        v_isShared_3874_ = v_isSharedCheck_3941_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3947_ = leanh::lean_ctor_get(v_l_3672_, 0);
                                v___x_3948_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3949_ = lean_nat_add(v___x_3948_, v_size_3947_);
                                if v_isShared_3676_ == 0 {
                                    leanh::lean_ctor_set(v___x_3675_, 4, v___x_3856_);
                                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3949_);
                                    v___x_3951_ = v___x_3675_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3952_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3952_,
                                        0,
                                        v___x_3949_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3952_,
                                        1,
                                        v_k_3670_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3952_,
                                        2,
                                        v_v_3671_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3952_,
                                        3,
                                        v_l_3672_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3952_,
                                        4,
                                        v___x_3856_,
                                    );
                                    v___x_3951_ = v_reuseFailAlloc_3952_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_3856_) == 0 {
                                v_l_3953_ = leanh::lean_ctor_get(v___x_3856_, 3);
                                leanh::lean_inc(v_l_3953_);
                                if leanh::lean_obj_tag(v_l_3953_) == 0 {
                                    v_r_3954_ = leanh::lean_ctor_get(v___x_3856_, 4);
                                    leanh::lean_inc(v_r_3954_);
                                    if leanh::lean_obj_tag(v_r_3954_) == 0 {
                                        v_size_3955_ = leanh::lean_ctor_get(v___x_3856_, 0);
                                        v_k_3956_ = leanh::lean_ctor_get(v___x_3856_, 1);
                                        v_v_3957_ = leanh::lean_ctor_get(v___x_3856_, 2);
                                        v_isSharedCheck_3971_ =
                                            (!leanh::lean_is_exclusive(v___x_3856_)) as u8;
                                        if v_isSharedCheck_3971_ == 0 {
                                            v_unused_3972_ =
                                                leanh::lean_ctor_get(v___x_3856_, 4);
                                            leanh::lean_dec(v_unused_3972_);
                                            v_unused_3973_ =
                                                leanh::lean_ctor_get(v___x_3856_, 3);
                                            leanh::lean_dec(v_unused_3973_);
                                            v___x_3959_ = v___x_3856_;
                                            v_isShared_3960_ = v_isSharedCheck_3971_;
                                            state = 40;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3957_);
                                            leanh::lean_inc(v_k_3956_);
                                            leanh::lean_inc(v_size_3955_);
                                            leanh::lean_dec(v___x_3856_);
                                            v___x_3959_ = leanh::lean_box(0);
                                            v_isShared_3960_ = v_isSharedCheck_3971_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_3974_ = leanh::lean_ctor_get(v___x_3856_, 1);
                                        v_v_3975_ = leanh::lean_ctor_get(v___x_3856_, 2);
                                        v_isSharedCheck_3999_ =
                                            (!leanh::lean_is_exclusive(v___x_3856_)) as u8;
                                        if v_isSharedCheck_3999_ == 0 {
                                            v_unused_4000_ =
                                                leanh::lean_ctor_get(v___x_3856_, 4);
                                            leanh::lean_dec(v_unused_4000_);
                                            v_unused_4001_ =
                                                leanh::lean_ctor_get(v___x_3856_, 3);
                                            leanh::lean_dec(v_unused_4001_);
                                            v_unused_4002_ =
                                                leanh::lean_ctor_get(v___x_3856_, 0);
                                            leanh::lean_dec(v_unused_4002_);
                                            v___x_3977_ = v___x_3856_;
                                            v_isShared_3978_ = v_isSharedCheck_3999_;
                                            state = 43;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_3975_);
                                            leanh::lean_inc(v_k_3974_);
                                            leanh::lean_dec(v___x_3856_);
                                            v___x_3977_ = leanh::lean_box(0);
                                            v_isShared_3978_ = v_isSharedCheck_3999_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_4003_ = leanh::lean_ctor_get(v___x_3856_, 4);
                                    leanh::lean_inc(v_r_4003_);
                                    if leanh::lean_obj_tag(v_r_4003_) == 0 {
                                        v_k_4004_ = leanh::lean_ctor_get(v___x_3856_, 1);
                                        v_v_4005_ = leanh::lean_ctor_get(v___x_3856_, 2);
                                        v_isSharedCheck_4017_ =
                                            (!leanh::lean_is_exclusive(v___x_3856_)) as u8;
                                        if v_isSharedCheck_4017_ == 0 {
                                            v_unused_4018_ =
                                                leanh::lean_ctor_get(v___x_3856_, 4);
                                            leanh::lean_dec(v_unused_4018_);
                                            v_unused_4019_ =
                                                leanh::lean_ctor_get(v___x_3856_, 3);
                                            leanh::lean_dec(v_unused_4019_);
                                            v_unused_4020_ =
                                                leanh::lean_ctor_get(v___x_3856_, 0);
                                            leanh::lean_dec(v_unused_4020_);
                                            v___x_4007_ = v___x_3856_;
                                            v_isShared_4008_ = v_isSharedCheck_4017_;
                                            state = 48;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4005_);
                                            leanh::lean_inc(v_k_4004_);
                                            leanh::lean_dec(v___x_3856_);
                                            v___x_4007_ = leanh::lean_box(0);
                                            v_isShared_4008_ = v_isSharedCheck_4017_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_4021_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3676_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_3675_,
                                                4,
                                                v___x_3856_,
                                            );
                                            leanh::lean_ctor_set(v___x_3675_, 3, v_r_4003_);
                                            leanh::lean_ctor_set(
                                                v___x_3675_,
                                                0,
                                                v___x_4021_,
                                            );
                                            v___x_4023_ = v___x_3675_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4024_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4024_,
                                                0,
                                                v___x_4021_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4024_,
                                                1,
                                                v_k_3670_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4024_,
                                                2,
                                                v_v_3671_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4024_,
                                                3,
                                                v_r_4003_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4024_,
                                                4,
                                                v___x_3856_,
                                            );
                                            v___x_4023_ = v_reuseFailAlloc_4024_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_4025_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_3676_ == 0 {
                                    leanh::lean_ctor_set(v___x_3675_, 4, v___x_3856_);
                                    leanh::lean_ctor_set(v___x_3675_, 3, v___x_3856_);
                                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_4025_);
                                    v___x_4027_ = v___x_3675_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4028_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4028_,
                                        0,
                                        v___x_4025_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4028_,
                                        1,
                                        v_k_3670_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4028_,
                                        2,
                                        v_v_3671_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4028_,
                                        3,
                                        v___x_3856_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4028_,
                                        4,
                                        v___x_3856_,
                                    );
                                    v___x_4027_ = v_reuseFailAlloc_4028_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3692_;
            }
            3 => {
                if leanh::lean_obj_tag(v_l_3683_) == 0 {
                    if leanh::lean_obj_tag(v_r_3684_) == 0 {
                        v_size_3697_ = leanh::lean_ctor_get(v_l_3683_, 0);
                        v_size_3698_ = leanh::lean_ctor_get(v_r_3684_, 0);
                        v_k_3699_ = leanh::lean_ctor_get(v_r_3684_, 1);
                        v_v_3700_ = leanh::lean_ctor_get(v_r_3684_, 2);
                        v_l_3701_ = leanh::lean_ctor_get(v_r_3684_, 3);
                        v_r_3702_ = leanh::lean_ctor_get(v_r_3684_, 4);
                        v___x_3703_ = leanh::lean_unsigned_to_nat(2);
                        v___x_3704_ = lean_nat_mul(v___x_3703_, v_size_3697_);
                        v___x_3705_ = lean_nat_dec_lt(v_size_3698_, v___x_3704_);
                        leanh::lean_dec(v___x_3704_);
                        if v___x_3705_ == 0 {
                            leanh::lean_inc(v_r_3702_);
                            leanh::lean_inc(v_l_3701_);
                            leanh::lean_inc(v_v_3700_);
                            leanh::lean_inc(v_k_3699_);
                            v_isSharedCheck_3735_ =
                                (!leanh::lean_is_exclusive(v_r_3684_)) as u8;
                            if v_isSharedCheck_3735_ == 0 {
                                v_unused_3736_ = leanh::lean_ctor_get(v_r_3684_, 4);
                                leanh::lean_dec(v_unused_3736_);
                                v_unused_3737_ = leanh::lean_ctor_get(v_r_3684_, 3);
                                leanh::lean_dec(v_unused_3737_);
                                v_unused_3738_ = leanh::lean_ctor_get(v_r_3684_, 2);
                                leanh::lean_dec(v_unused_3738_);
                                v_unused_3739_ = leanh::lean_ctor_get(v_r_3684_, 1);
                                leanh::lean_dec(v_unused_3739_);
                                v_unused_3740_ = leanh::lean_ctor_get(v_r_3684_, 0);
                                leanh::lean_dec(v_unused_3740_);
                                v___x_3707_ = v_r_3684_;
                                v_isShared_3708_ = v_isSharedCheck_3735_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v_r_3684_);
                                v___x_3707_ = leanh::lean_box(0);
                                v_isShared_3708_ = v_isSharedCheck_3735_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3675_);
                            v___x_3741_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3742_ = lean_nat_add(v___x_3741_, v_size_3680_);
                            leanh::lean_dec(v_size_3680_);
                            v___x_3743_ = lean_nat_add(v___x_3742_, v_size_3679_);
                            leanh::lean_dec(v___x_3742_);
                            v___x_3744_ = lean_nat_add(v___x_3741_, v_size_3679_);
                            v___x_3745_ = lean_nat_add(v___x_3744_, v_size_3698_);
                            leanh::lean_dec(v___x_3744_);
                            leanh::lean_inc_ref(v_r_3673_);
                            if v_isShared_3696_ == 0 {
                                leanh::lean_ctor_set(v___x_3695_, 4, v_r_3673_);
                                leanh::lean_ctor_set(v___x_3695_, 3, v_r_3684_);
                                leanh::lean_ctor_set(v___x_3695_, 2, v_v_3671_);
                                leanh::lean_ctor_set(v___x_3695_, 1, v_k_3670_);
                                leanh::lean_ctor_set(v___x_3695_, 0, v___x_3745_);
                                v___x_3747_ = v___x_3695_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_3760_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3745_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_k_3670_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_v_3671_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_r_3684_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 4, v_r_3673_);
                                v___x_3747_ = v_reuseFailAlloc_3760_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_3683_, 5);
                        leanh::lean_del_object(v___x_3695_);
                        leanh::lean_dec(v_v_3682_);
                        leanh::lean_dec(v_k_3681_);
                        leanh::lean_dec(v_size_3680_);
                        leanh::lean_dec_ref_known(v_r_3673_, 5);
                        leanh::lean_del_object(v___x_3675_);
                        leanh::lean_dec(v_v_3671_);
                        leanh::lean_dec(v_k_3670_);
                        v___x_3761_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
                        v___x_3762_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_3761_);
                        return v___x_3762_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3695_);
                    leanh::lean_dec(v_r_3684_);
                    leanh::lean_dec(v_v_3682_);
                    leanh::lean_dec(v_k_3681_);
                    leanh::lean_dec(v_size_3680_);
                    leanh::lean_dec_ref_known(v_r_3673_, 5);
                    leanh::lean_del_object(v___x_3675_);
                    leanh::lean_dec(v_v_3671_);
                    leanh::lean_dec(v_k_3670_);
                    v___x_3763_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
                    v___x_3764_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_3763_);
                    return v___x_3764_;
                }
            }
            4 => {
                v___x_3709_ = leanh::lean_unsigned_to_nat(1);
                v___x_3710_ = lean_nat_add(v___x_3709_, v_size_3680_);
                leanh::lean_dec(v_size_3680_);
                v___x_3711_ = lean_nat_add(v___x_3710_, v_size_3679_);
                leanh::lean_dec(v___x_3710_);
                v___x_3723_ = lean_nat_add(v___x_3709_, v_size_3697_);
                if leanh::lean_obj_tag(v_l_3701_) == 0 {
                    v_size_3733_ = leanh::lean_ctor_get(v_l_3701_, 0);
                    leanh::lean_inc(v_size_3733_);
                    v___y_3725_ = v_size_3733_;
                    state = 8;
                    continue;
                } else {
                    v___x_3734_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3725_ = v___x_3734_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3716_ = lean_nat_add(v___y_3714_, v___y_3715_);
                leanh::lean_dec(v___y_3715_);
                leanh::lean_dec(v___y_3714_);
                if v_isShared_3708_ == 0 {
                    leanh::lean_ctor_set(v___x_3707_, 4, v_r_3673_);
                    leanh::lean_ctor_set(v___x_3707_, 3, v_r_3702_);
                    leanh::lean_ctor_set(v___x_3707_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v___x_3707_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v___x_3707_, 0, v___x_3716_);
                    v___x_3718_ = v___x_3707_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3722_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3716_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 3, v_r_3702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 4, v_r_3673_);
                    v___x_3718_ = v_reuseFailAlloc_3722_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3696_ == 0 {
                    leanh::lean_ctor_set(v___x_3695_, 4, v___x_3718_);
                    leanh::lean_ctor_set(v___x_3695_, 3, v___y_3713_);
                    leanh::lean_ctor_set(v___x_3695_, 2, v_v_3700_);
                    leanh::lean_ctor_set(v___x_3695_, 1, v_k_3699_);
                    leanh::lean_ctor_set(v___x_3695_, 0, v___x_3711_);
                    v___x_3720_ = v___x_3695_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3721_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_k_3699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_v_3700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 3, v___y_3713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 4, v___x_3718_);
                    v___x_3720_ = v_reuseFailAlloc_3721_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3720_;
            }
            8 => {
                v___x_3726_ = lean_nat_add(v___x_3723_, v___y_3725_);
                leanh::lean_dec(v___y_3725_);
                leanh::lean_dec(v___x_3723_);
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v_l_3701_);
                    leanh::lean_ctor_set(v___x_3675_, 3, v_l_3683_);
                    leanh::lean_ctor_set(v___x_3675_, 2, v_v_3682_);
                    leanh::lean_ctor_set(v___x_3675_, 1, v_k_3681_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3726_);
                    v___x_3728_ = v___x_3675_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3726_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_k_3681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_v_3682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 3, v_l_3683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_l_3701_);
                    v___x_3728_ = v_reuseFailAlloc_3732_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3729_ = lean_nat_add(v___x_3709_, v_size_3679_);
                if leanh::lean_obj_tag(v_r_3702_) == 0 {
                    v_size_3730_ = leanh::lean_ctor_get(v_r_3702_, 0);
                    leanh::lean_inc(v_size_3730_);
                    v___y_3713_ = v___x_3728_;
                    v___y_3714_ = v___x_3729_;
                    v___y_3715_ = v_size_3730_;
                    state = 5;
                    continue;
                } else {
                    v___x_3731_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3713_ = v___x_3728_;
                    v___y_3714_ = v___x_3729_;
                    v___y_3715_ = v___x_3731_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3754_ = (!leanh::lean_is_exclusive(v_r_3673_)) as u8;
                if v_isSharedCheck_3754_ == 0 {
                    v_unused_3755_ = leanh::lean_ctor_get(v_r_3673_, 4);
                    leanh::lean_dec(v_unused_3755_);
                    v_unused_3756_ = leanh::lean_ctor_get(v_r_3673_, 3);
                    leanh::lean_dec(v_unused_3756_);
                    v_unused_3757_ = leanh::lean_ctor_get(v_r_3673_, 2);
                    leanh::lean_dec(v_unused_3757_);
                    v_unused_3758_ = leanh::lean_ctor_get(v_r_3673_, 1);
                    leanh::lean_dec(v_unused_3758_);
                    v_unused_3759_ = leanh::lean_ctor_get(v_r_3673_, 0);
                    leanh::lean_dec(v_unused_3759_);
                    v___x_3749_ = v_r_3673_;
                    v_isShared_3750_ = v_isSharedCheck_3754_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_3673_);
                    v___x_3749_ = leanh::lean_box(0);
                    v_isShared_3750_ = v_isSharedCheck_3754_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3750_ == 0 {
                    leanh::lean_ctor_set(v___x_3749_, 4, v___x_3747_);
                    leanh::lean_ctor_set(v___x_3749_, 3, v_l_3683_);
                    leanh::lean_ctor_set(v___x_3749_, 2, v_v_3682_);
                    leanh::lean_ctor_set(v___x_3749_, 1, v_k_3681_);
                    leanh::lean_ctor_set(v___x_3749_, 0, v___x_3743_);
                    v___x_3752_ = v___x_3749_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3743_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_k_3681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_v_3682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_l_3683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 4, v___x_3747_);
                    v___x_3752_ = v_reuseFailAlloc_3753_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3752_;
            }
            13 => {
                return v___x_3775_;
            }
            14 => {
                v_size_3785_ = leanh::lean_ctor_get(v_r_3778_, 0);
                v___x_3786_ = leanh::lean_unsigned_to_nat(1);
                v___x_3787_ = lean_nat_add(v___x_3786_, v_size_3779_);
                leanh::lean_dec(v_size_3779_);
                v___x_3788_ = lean_nat_add(v___x_3786_, v_size_3785_);
                if v_isShared_3784_ == 0 {
                    leanh::lean_ctor_set(v___x_3783_, 4, v_r_3673_);
                    leanh::lean_ctor_set(v___x_3783_, 3, v_r_3778_);
                    leanh::lean_ctor_set(v___x_3783_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v___x_3783_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v___x_3783_, 0, v___x_3788_);
                    v___x_3790_ = v___x_3783_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 3, v_r_3778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 4, v_r_3673_);
                    v___x_3790_ = v_reuseFailAlloc_3794_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v___x_3790_);
                    leanh::lean_ctor_set(v___x_3675_, 3, v_l_3777_);
                    leanh::lean_ctor_set(v___x_3675_, 2, v_v_3781_);
                    leanh::lean_ctor_set(v___x_3675_, 1, v_k_3780_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3787_);
                    v___x_3792_ = v___x_3675_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3793_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_k_3780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_v_3781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 3, v_l_3777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 4, v___x_3790_);
                    v___x_3792_ = v_reuseFailAlloc_3793_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3792_;
            }
            17 => {
                v___x_3803_ = leanh::lean_unsigned_to_nat(3);
                v___x_3804_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_3802_ == 0 {
                    leanh::lean_ctor_set(v___x_3801_, 3, v_r_3778_);
                    leanh::lean_ctor_set(v___x_3801_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v___x_3801_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v___x_3801_, 0, v___x_3804_);
                    v___x_3806_ = v___x_3801_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3810_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 3, v_r_3778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 4, v_r_3778_);
                    v___x_3806_ = v_reuseFailAlloc_3810_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v___x_3806_);
                    leanh::lean_ctor_set(v___x_3675_, 3, v_l_3777_);
                    leanh::lean_ctor_set(v___x_3675_, 2, v_v_3799_);
                    leanh::lean_ctor_set(v___x_3675_, 1, v_k_3798_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3803_);
                    v___x_3808_ = v___x_3675_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_k_3798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 2, v_v_3799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 3, v_l_3777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 4, v___x_3806_);
                    v___x_3808_ = v_reuseFailAlloc_3809_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3808_;
            }
            20 => {
                v_k_3821_ = leanh::lean_ctor_get(v_r_3815_, 1);
                v_v_3822_ = leanh::lean_ctor_get(v_r_3815_, 2);
                v_isSharedCheck_3837_ = (!leanh::lean_is_exclusive(v_r_3815_)) as u8;
                if v_isSharedCheck_3837_ == 0 {
                    v_unused_3838_ = leanh::lean_ctor_get(v_r_3815_, 4);
                    leanh::lean_dec(v_unused_3838_);
                    v_unused_3839_ = leanh::lean_ctor_get(v_r_3815_, 3);
                    leanh::lean_dec(v_unused_3839_);
                    v_unused_3840_ = leanh::lean_ctor_get(v_r_3815_, 0);
                    leanh::lean_dec(v_unused_3840_);
                    v___x_3824_ = v_r_3815_;
                    v_isShared_3825_ = v_isSharedCheck_3837_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3822_);
                    leanh::lean_inc(v_k_3821_);
                    leanh::lean_dec(v_r_3815_);
                    v___x_3824_ = leanh::lean_box(0);
                    v_isShared_3825_ = v_isSharedCheck_3837_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3826_ = leanh::lean_unsigned_to_nat(3);
                v___x_3827_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_3825_ == 0 {
                    leanh::lean_ctor_set(v___x_3824_, 4, v_l_3777_);
                    leanh::lean_ctor_set(v___x_3824_, 3, v_l_3777_);
                    leanh::lean_ctor_set(v___x_3824_, 2, v_v_3817_);
                    leanh::lean_ctor_set(v___x_3824_, 1, v_k_3816_);
                    leanh::lean_ctor_set(v___x_3824_, 0, v___x_3827_);
                    v___x_3829_ = v___x_3824_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_k_3816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_v_3817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_l_3777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 4, v_l_3777_);
                    v___x_3829_ = v_reuseFailAlloc_3836_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_3820_ == 0 {
                    leanh::lean_ctor_set(v___x_3819_, 4, v_l_3777_);
                    leanh::lean_ctor_set(v___x_3819_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v___x_3819_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v___x_3819_, 0, v___x_3827_);
                    v___x_3831_ = v___x_3819_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3835_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_l_3777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 4, v_l_3777_);
                    v___x_3831_ = v_reuseFailAlloc_3835_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v___x_3831_);
                    leanh::lean_ctor_set(v___x_3675_, 3, v___x_3829_);
                    leanh::lean_ctor_set(v___x_3675_, 2, v_v_3822_);
                    leanh::lean_ctor_set(v___x_3675_, 1, v_k_3821_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3826_);
                    v___x_3833_ = v___x_3675_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_k_3821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 2, v_v_3822_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 3, v___x_3829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 4, v___x_3831_);
                    v___x_3833_ = v_reuseFailAlloc_3834_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3833_;
            }
            25 => {
                return v___x_3847_;
            }
            26 => {
                return v___x_3851_;
            }
            27 => {
                return v___x_3854_;
            }
            28 => {
                return v___x_3870_;
            }
            29 => {
                if leanh::lean_obj_tag(v_l_3861_) == 0 {
                    if leanh::lean_obj_tag(v_r_3862_) == 0 {
                        v_size_3875_ = leanh::lean_ctor_get(v_l_3861_, 0);
                        v_k_3876_ = leanh::lean_ctor_get(v_l_3861_, 1);
                        v_v_3877_ = leanh::lean_ctor_get(v_l_3861_, 2);
                        v_l_3878_ = leanh::lean_ctor_get(v_l_3861_, 3);
                        v_r_3879_ = leanh::lean_ctor_get(v_l_3861_, 4);
                        v_size_3880_ = leanh::lean_ctor_get(v_r_3862_, 0);
                        v___x_3881_ = leanh::lean_unsigned_to_nat(2);
                        v___x_3882_ = lean_nat_mul(v___x_3881_, v_size_3880_);
                        v___x_3883_ = lean_nat_dec_lt(v_size_3875_, v___x_3882_);
                        leanh::lean_dec(v___x_3882_);
                        if v___x_3883_ == 0 {
                            leanh::lean_inc(v_r_3879_);
                            leanh::lean_inc(v_l_3878_);
                            leanh::lean_inc(v_v_3877_);
                            leanh::lean_inc(v_k_3876_);
                            v_isSharedCheck_3912_ =
                                (!leanh::lean_is_exclusive(v_l_3861_)) as u8;
                            if v_isSharedCheck_3912_ == 0 {
                                v_unused_3913_ = leanh::lean_ctor_get(v_l_3861_, 4);
                                leanh::lean_dec(v_unused_3913_);
                                v_unused_3914_ = leanh::lean_ctor_get(v_l_3861_, 3);
                                leanh::lean_dec(v_unused_3914_);
                                v_unused_3915_ = leanh::lean_ctor_get(v_l_3861_, 2);
                                leanh::lean_dec(v_unused_3915_);
                                v_unused_3916_ = leanh::lean_ctor_get(v_l_3861_, 1);
                                leanh::lean_dec(v_unused_3916_);
                                v_unused_3917_ = leanh::lean_ctor_get(v_l_3861_, 0);
                                leanh::lean_dec(v_unused_3917_);
                                v___x_3885_ = v_l_3861_;
                                v_isShared_3886_ = v_isSharedCheck_3912_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_3861_);
                                v___x_3885_ = leanh::lean_box(0);
                                v_isShared_3886_ = v_isSharedCheck_3912_;
                                state = 30;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3675_);
                            v___x_3918_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3919_ = lean_nat_add(v___x_3918_, v_size_3857_);
                            v___x_3920_ = lean_nat_add(v___x_3919_, v_size_3858_);
                            leanh::lean_dec(v_size_3858_);
                            v___x_3921_ = lean_nat_add(v___x_3919_, v_size_3875_);
                            leanh::lean_dec(v___x_3919_);
                            leanh::lean_inc_ref(v_l_3672_);
                            if v_isShared_3874_ == 0 {
                                leanh::lean_ctor_set(v___x_3873_, 4, v_l_3861_);
                                leanh::lean_ctor_set(v___x_3873_, 3, v_l_3672_);
                                leanh::lean_ctor_set(v___x_3873_, 2, v_v_3671_);
                                leanh::lean_ctor_set(v___x_3873_, 1, v_k_3670_);
                                leanh::lean_ctor_set(v___x_3873_, 0, v___x_3921_);
                                v___x_3923_ = v___x_3873_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_3936_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3921_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_k_3670_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_v_3671_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_l_3672_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_l_3861_);
                                v___x_3923_ = v_reuseFailAlloc_3936_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_3861_, 5);
                        leanh::lean_del_object(v___x_3873_);
                        leanh::lean_dec(v_v_3860_);
                        leanh::lean_dec(v_k_3859_);
                        leanh::lean_dec(v_size_3858_);
                        leanh::lean_dec_ref_known(v_l_3672_, 5);
                        leanh::lean_del_object(v___x_3675_);
                        leanh::lean_dec(v_v_3671_);
                        leanh::lean_dec(v_k_3670_);
                        v___x_3937_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
                        v___x_3938_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_3937_);
                        return v___x_3938_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3873_);
                    leanh::lean_dec(v_r_3862_);
                    leanh::lean_dec(v_v_3860_);
                    leanh::lean_dec(v_k_3859_);
                    leanh::lean_dec(v_size_3858_);
                    leanh::lean_dec_ref_known(v_l_3672_, 5);
                    leanh::lean_del_object(v___x_3675_);
                    leanh::lean_dec(v_v_3671_);
                    leanh::lean_dec(v_k_3670_);
                    v___x_3939_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
                    v___x_3940_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_3939_);
                    return v___x_3940_;
                }
            }
            30 => {
                v___x_3887_ = leanh::lean_unsigned_to_nat(1);
                v___x_3888_ = lean_nat_add(v___x_3887_, v_size_3857_);
                v___x_3889_ = lean_nat_add(v___x_3888_, v_size_3858_);
                leanh::lean_dec(v_size_3858_);
                if leanh::lean_obj_tag(v_l_3878_) == 0 {
                    v_size_3910_ = leanh::lean_ctor_get(v_l_3878_, 0);
                    leanh::lean_inc(v_size_3910_);
                    v___y_3902_ = v_size_3910_;
                    state = 34;
                    continue;
                } else {
                    v___x_3911_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3902_ = v___x_3911_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_3894_ = lean_nat_add(v___y_3892_, v___y_3893_);
                leanh::lean_dec(v___y_3893_);
                leanh::lean_dec(v___y_3892_);
                if v_isShared_3886_ == 0 {
                    leanh::lean_ctor_set(v___x_3885_, 4, v_r_3862_);
                    leanh::lean_ctor_set(v___x_3885_, 3, v_r_3879_);
                    leanh::lean_ctor_set(v___x_3885_, 2, v_v_3860_);
                    leanh::lean_ctor_set(v___x_3885_, 1, v_k_3859_);
                    leanh::lean_ctor_set(v___x_3885_, 0, v___x_3894_);
                    v___x_3896_ = v___x_3885_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3900_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_k_3859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 2, v_v_3860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 3, v_r_3879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 4, v_r_3862_);
                    v___x_3896_ = v_reuseFailAlloc_3900_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3874_ == 0 {
                    leanh::lean_ctor_set(v___x_3873_, 4, v___x_3896_);
                    leanh::lean_ctor_set(v___x_3873_, 3, v___y_3891_);
                    leanh::lean_ctor_set(v___x_3873_, 2, v_v_3877_);
                    leanh::lean_ctor_set(v___x_3873_, 1, v_k_3876_);
                    leanh::lean_ctor_set(v___x_3873_, 0, v___x_3889_);
                    v___x_3898_ = v___x_3873_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3899_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3889_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_k_3876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 2, v_v_3877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 3, v___y_3891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 4, v___x_3896_);
                    v___x_3898_ = v_reuseFailAlloc_3899_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3898_;
            }
            34 => {
                v___x_3903_ = lean_nat_add(v___x_3888_, v___y_3902_);
                leanh::lean_dec(v___y_3902_);
                leanh::lean_dec(v___x_3888_);
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v_l_3878_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3903_);
                    v___x_3905_ = v___x_3675_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 3, v_l_3672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 4, v_l_3878_);
                    v___x_3905_ = v_reuseFailAlloc_3909_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3906_ = lean_nat_add(v___x_3887_, v_size_3880_);
                if leanh::lean_obj_tag(v_r_3879_) == 0 {
                    v_size_3907_ = leanh::lean_ctor_get(v_r_3879_, 0);
                    leanh::lean_inc(v_size_3907_);
                    v___y_3891_ = v___x_3905_;
                    v___y_3892_ = v___x_3906_;
                    v___y_3893_ = v_size_3907_;
                    state = 31;
                    continue;
                } else {
                    v___x_3908_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3891_ = v___x_3905_;
                    v___y_3892_ = v___x_3906_;
                    v___y_3893_ = v___x_3908_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_3930_ = (!leanh::lean_is_exclusive(v_l_3672_)) as u8;
                if v_isSharedCheck_3930_ == 0 {
                    v_unused_3931_ = leanh::lean_ctor_get(v_l_3672_, 4);
                    leanh::lean_dec(v_unused_3931_);
                    v_unused_3932_ = leanh::lean_ctor_get(v_l_3672_, 3);
                    leanh::lean_dec(v_unused_3932_);
                    v_unused_3933_ = leanh::lean_ctor_get(v_l_3672_, 2);
                    leanh::lean_dec(v_unused_3933_);
                    v_unused_3934_ = leanh::lean_ctor_get(v_l_3672_, 1);
                    leanh::lean_dec(v_unused_3934_);
                    v_unused_3935_ = leanh::lean_ctor_get(v_l_3672_, 0);
                    leanh::lean_dec(v_unused_3935_);
                    v___x_3925_ = v_l_3672_;
                    v_isShared_3926_ = v_isSharedCheck_3930_;
                    state = 37;
                    continue;
                } else {
                    leanh::lean_dec(v_l_3672_);
                    v___x_3925_ = leanh::lean_box(0);
                    v_isShared_3926_ = v_isSharedCheck_3930_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3926_ == 0 {
                    leanh::lean_ctor_set(v___x_3925_, 4, v_r_3862_);
                    leanh::lean_ctor_set(v___x_3925_, 3, v___x_3923_);
                    leanh::lean_ctor_set(v___x_3925_, 2, v_v_3860_);
                    leanh::lean_ctor_set(v___x_3925_, 1, v_k_3859_);
                    leanh::lean_ctor_set(v___x_3925_, 0, v___x_3920_);
                    v___x_3928_ = v___x_3925_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3929_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_k_3859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_v_3860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 3, v___x_3923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 4, v_r_3862_);
                    v___x_3928_ = v_reuseFailAlloc_3929_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3928_;
            }
            39 => {
                return v___x_3951_;
            }
            40 => {
                v_size_3961_ = leanh::lean_ctor_get(v_l_3953_, 0);
                v___x_3962_ = leanh::lean_unsigned_to_nat(1);
                v___x_3963_ = lean_nat_add(v___x_3962_, v_size_3955_);
                leanh::lean_dec(v_size_3955_);
                v___x_3964_ = lean_nat_add(v___x_3962_, v_size_3961_);
                if v_isShared_3960_ == 0 {
                    leanh::lean_ctor_set(v___x_3959_, 4, v_l_3953_);
                    leanh::lean_ctor_set(v___x_3959_, 3, v_l_3672_);
                    leanh::lean_ctor_set(v___x_3959_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v___x_3959_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v___x_3959_, 0, v___x_3964_);
                    v___x_3966_ = v___x_3959_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3970_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 3, v_l_3672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 4, v_l_3953_);
                    v___x_3966_ = v_reuseFailAlloc_3970_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v_r_3954_);
                    leanh::lean_ctor_set(v___x_3675_, 3, v___x_3966_);
                    leanh::lean_ctor_set(v___x_3675_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_3675_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3963_);
                    v___x_3968_ = v___x_3675_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 3, v___x_3966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 4, v_r_3954_);
                    v___x_3968_ = v_reuseFailAlloc_3969_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3968_;
            }
            43 => {
                v_k_3979_ = leanh::lean_ctor_get(v_l_3953_, 1);
                v_v_3980_ = leanh::lean_ctor_get(v_l_3953_, 2);
                v_isSharedCheck_3995_ = (!leanh::lean_is_exclusive(v_l_3953_)) as u8;
                if v_isSharedCheck_3995_ == 0 {
                    v_unused_3996_ = leanh::lean_ctor_get(v_l_3953_, 4);
                    leanh::lean_dec(v_unused_3996_);
                    v_unused_3997_ = leanh::lean_ctor_get(v_l_3953_, 3);
                    leanh::lean_dec(v_unused_3997_);
                    v_unused_3998_ = leanh::lean_ctor_get(v_l_3953_, 0);
                    leanh::lean_dec(v_unused_3998_);
                    v___x_3982_ = v_l_3953_;
                    v_isShared_3983_ = v_isSharedCheck_3995_;
                    state = 44;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3980_);
                    leanh::lean_inc(v_k_3979_);
                    leanh::lean_dec(v_l_3953_);
                    v___x_3982_ = leanh::lean_box(0);
                    v_isShared_3983_ = v_isSharedCheck_3995_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3984_ = leanh::lean_unsigned_to_nat(3);
                v___x_3985_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_3983_ == 0 {
                    leanh::lean_ctor_set(v___x_3982_, 4, v_r_3954_);
                    leanh::lean_ctor_set(v___x_3982_, 3, v_r_3954_);
                    leanh::lean_ctor_set(v___x_3982_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v___x_3982_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v___x_3982_, 0, v___x_3985_);
                    v___x_3987_ = v___x_3982_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 3, v_r_3954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 4, v_r_3954_);
                    v___x_3987_ = v_reuseFailAlloc_3994_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3978_ == 0 {
                    leanh::lean_ctor_set(v___x_3977_, 3, v_r_3954_);
                    leanh::lean_ctor_set(v___x_3977_, 0, v___x_3985_);
                    v___x_3989_ = v___x_3977_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_k_3974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_v_3975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_r_3954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 4, v_r_3954_);
                    v___x_3989_ = v_reuseFailAlloc_3993_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v___x_3989_);
                    leanh::lean_ctor_set(v___x_3675_, 3, v___x_3987_);
                    leanh::lean_ctor_set(v___x_3675_, 2, v_v_3980_);
                    leanh::lean_ctor_set(v___x_3675_, 1, v_k_3979_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3984_);
                    v___x_3991_ = v___x_3675_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_k_3979_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 2, v_v_3980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 3, v___x_3987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 4, v___x_3989_);
                    v___x_3991_ = v_reuseFailAlloc_3992_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3991_;
            }
            48 => {
                v___x_4009_ = leanh::lean_unsigned_to_nat(3);
                v___x_4010_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_4008_ == 0 {
                    leanh::lean_ctor_set(v___x_4007_, 4, v_l_3953_);
                    leanh::lean_ctor_set(v___x_4007_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v___x_4007_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v___x_4007_, 0, v___x_4010_);
                    v___x_4012_ = v___x_4007_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4016_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_k_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 2, v_v_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 3, v_l_3953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 4, v_l_3953_);
                    v___x_4012_ = v_reuseFailAlloc_4016_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 4, v_r_4003_);
                    leanh::lean_ctor_set(v___x_3675_, 3, v___x_4012_);
                    leanh::lean_ctor_set(v___x_3675_, 2, v_v_4005_);
                    leanh::lean_ctor_set(v___x_3675_, 1, v_k_4004_);
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_4009_);
                    v___x_4014_ = v___x_3675_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_4015_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_k_4004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 2, v_v_4005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 3, v___x_4012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 4, v_r_4003_);
                    v___x_4014_ = v_reuseFailAlloc_4015_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_4014_;
            }
            51 => {
                return v___x_4023_;
            }
            52 => {
                return v___x_4027_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(
    mut v_init_4032_: *mut leanh::LeanObject,
    mut v_x_4033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4033_) == 0 {
                    v_k_4034_ = leanh::lean_ctor_get(v_x_4033_, 1);
                    leanh::lean_inc(v_k_4034_);
                    v_v_4035_ = leanh::lean_ctor_get(v_x_4033_, 2);
                    leanh::lean_inc(v_v_4035_);
                    v_l_4036_ = leanh::lean_ctor_get(v_x_4033_, 3);
                    leanh::lean_inc(v_l_4036_);
                    v_r_4037_ = leanh::lean_ctor_get(v_x_4033_, 4);
                    leanh::lean_inc(v_r_4037_);
                    leanh::lean_dec_ref_known(v_x_4033_, 5);
                    v___x_4038_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_4032_, v_l_4036_);
                    v___x_4039_ = 1;
                    v___x_4040_ = l_Lean_Name_toString(v_k_4034_, v___x_4039_);
                    v___x_4041_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4041_, 0, v_v_4035_);
                    v___x_4042_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_4040_, v___x_4041_, v___x_4038_);
                    v_init_4032_ = v___x_4042_;
                    v_x_4033_ = v_r_4037_;
                    state = 0;
                    continue;
                } else {
                    return v_init_4032_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(
    mut v_m_4044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4045_ = leanh::lean_box(1);
    v___x_4046_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_4045_, v_m_4044_);
    v___x_4047_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4047_, 0, v___x_4046_);
    return v___x_4047_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(
    mut v_a_4048_: *mut leanh::LeanObject,
    mut v_a_4049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4048_) == 0 {
                    v___x_4050_ = lean_array_to_list(v_a_4049_);
                    return v___x_4050_;
                } else {
                    v_head_4051_ = leanh::lean_ctor_get(v_a_4048_, 0);
                    leanh::lean_inc(v_head_4051_);
                    v_tail_4052_ = leanh::lean_ctor_get(v_a_4048_, 1);
                    leanh::lean_inc(v_tail_4052_);
                    leanh::lean_dec_ref_known(v_a_4048_, 2);
                    v___x_4053_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_4049_,
                        v_head_4051_,
                    );
                    v_a_4048_ = v_tail_4052_;
                    v_a_4049_ = v___x_4053_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(
    mut v_x_4063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_idx_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_platform_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanHash_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_configHash_4068_: u64 = 0;
    let mut v_options_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_idx_4064_ = leanh::lean_ctor_get(v_x_4063_, 0);
    leanh::lean_inc(v_idx_4064_);
    v_name_4065_ = leanh::lean_ctor_get(v_x_4063_, 1);
    leanh::lean_inc(v_name_4065_);
    v_platform_4066_ = leanh::lean_ctor_get(v_x_4063_, 2);
    leanh::lean_inc_ref(v_platform_4066_);
    v_leanHash_4067_ = leanh::lean_ctor_get(v_x_4063_, 3);
    leanh::lean_inc_ref(v_leanHash_4067_);
    v_configHash_4068_ = leanh::lean_ctor_get_uint64(
        v_x_4063_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
    );
    v_options_4069_ = leanh::lean_ctor_get(v_x_4063_, 4);
    leanh::lean_inc(v_options_4069_);
    leanh::lean_dec_ref(v_x_4063_);
    v___x_4070_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0;
    v___x_4071_ = l_Lean_JsonNumber_fromNat(v_idx_4064_);
    v___x_4072_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4072_, 0, v___x_4071_);
    v___x_4073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4073_, 0, v___x_4070_);
    leanh::lean_ctor_set(v___x_4073_, 1, v___x_4072_);
    v___x_4074_ = leanh::lean_box(0);
    v___x_4075_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4075_, 0, v___x_4073_);
    leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
    v___x_4076_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1;
    v___x_4077_ = 1;
    v___x_4078_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_4065_,
        v___x_4077_,
    );
    v___x_4079_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4079_, 0, v___x_4078_);
    v___x_4080_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4080_, 0, v___x_4076_);
    leanh::lean_ctor_set(v___x_4080_, 1, v___x_4079_);
    v___x_4081_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4081_, 0, v___x_4080_);
    leanh::lean_ctor_set(v___x_4081_, 1, v___x_4074_);
    v___x_4082_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2;
    v___x_4083_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4083_, 0, v_platform_4066_);
    v___x_4084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4084_, 0, v___x_4082_);
    leanh::lean_ctor_set(v___x_4084_, 1, v___x_4083_);
    v___x_4085_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4085_, 0, v___x_4084_);
    leanh::lean_ctor_set(v___x_4085_, 1, v___x_4074_);
    v___x_4086_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3;
    v___x_4087_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4087_, 0, v_leanHash_4067_);
    v___x_4088_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4088_, 0, v___x_4086_);
    leanh::lean_ctor_set(v___x_4088_, 1, v___x_4087_);
    v___x_4089_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4089_, 0, v___x_4088_);
    leanh::lean_ctor_set(v___x_4089_, 1, v___x_4074_);
    v___x_4090_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4;
    v___x_4091_ = l_Lake_lowerHexUInt64(v_configHash_4068_);
    v___x_4092_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4092_, 0, v___x_4091_);
    v___x_4093_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4093_, 0, v___x_4090_);
    leanh::lean_ctor_set(v___x_4093_, 1, v___x_4092_);
    v___x_4094_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4094_, 0, v___x_4093_);
    leanh::lean_ctor_set(v___x_4094_, 1, v___x_4074_);
    v___x_4095_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5;
    v___x_4096_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_4069_);
    v___x_4097_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4097_, 0, v___x_4095_);
    leanh::lean_ctor_set(v___x_4097_, 1, v___x_4096_);
    v___x_4098_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4098_, 0, v___x_4097_);
    leanh::lean_ctor_set(v___x_4098_, 1, v___x_4074_);
    v___x_4099_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4099_, 0, v___x_4098_);
    leanh::lean_ctor_set(v___x_4099_, 1, v___x_4074_);
    v___x_4100_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4100_, 0, v___x_4094_);
    leanh::lean_ctor_set(v___x_4100_, 1, v___x_4099_);
    v___x_4101_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4101_, 0, v___x_4089_);
    leanh::lean_ctor_set(v___x_4101_, 1, v___x_4100_);
    v___x_4102_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4102_, 0, v___x_4085_);
    leanh::lean_ctor_set(v___x_4102_, 1, v___x_4101_);
    v___x_4103_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4103_, 0, v___x_4081_);
    leanh::lean_ctor_set(v___x_4103_, 1, v___x_4102_);
    v___x_4104_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4104_, 0, v___x_4075_);
    leanh::lean_ctor_set(v___x_4104_, 1, v___x_4103_);
    v___x_4105_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6;
    v___x_4106_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_4104_, v___x_4105_);
    v___x_4107_ = l_Lean_Json_mkObj(v___x_4106_);
    leanh::lean_dec(v___x_4106_);
    return v___x_4107_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4108_: *mut leanh::LeanObject,
    mut v_msg_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4110_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_4109_);
    return v___x_4110_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(
    mut v_00_u03b2_4111_: *mut leanh::LeanObject,
    mut v_k_4112_: *mut leanh::LeanObject,
    mut v_v_4113_: *mut leanh::LeanObject,
    mut v_t_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4115_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_4112_, v_v_4113_, v_t_4114_);
    return v___x_4115_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(
    mut v_init_4116_: *mut leanh::LeanObject,
    mut v_t_4117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_4116_, v_t_4117_);
    return v___x_4118_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(
    mut v_j_4121_: *mut leanh::LeanObject,
    mut v_k_4122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4123_ = l_Lean_Json_getObjValD(v_j_4121_, v_k_4122_);
    v___x_4124_ = l_Lean_Json_getNat_x3f(v___x_4123_);
    return v___x_4124_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(
    mut v_j_4125_: *mut leanh::LeanObject,
    mut v_k_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_4125_, v_k_4126_);
    leanh::lean_dec_ref(v_k_4126_);
    return v_res_4127_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(
    mut v_j_4128_: *mut leanh::LeanObject,
    mut v_k_4129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4130_ = l_Lean_Json_getObjValD(v_j_4128_, v_k_4129_);
    v___x_4131_ = l_Lean_Name_fromJson_x3f(v___x_4130_);
    return v___x_4131_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(
    mut v_j_4132_: *mut leanh::LeanObject,
    mut v_k_4133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_4132_, v_k_4133_);
    leanh::lean_dec_ref(v_k_4133_);
    return v_res_4134_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(
    mut v_j_4135_: *mut leanh::LeanObject,
    mut v_k_4136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_Json_getObjValD(v_j_4135_, v_k_4136_);
    v___x_4138_ = l_Lean_Json_getStr_x3f(v___x_4137_);
    return v___x_4138_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(
    mut v_j_4139_: *mut leanh::LeanObject,
    mut v_k_4140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4141_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_4139_, v_k_4140_);
    leanh::lean_dec_ref(v_k_4140_);
    return v_res_4141_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(
    mut v_j_4142_: *mut leanh::LeanObject,
    mut v_k_4143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4144_ = l_Lean_Json_getObjValD(v_j_4142_, v_k_4143_);
    v___x_4145_ = l_Lake_Hash_fromJson_x3f(v___x_4144_);
    return v___x_4145_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(
    mut v_j_4146_: *mut leanh::LeanObject,
    mut v_k_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_4146_, v_k_4147_);
    leanh::lean_dec_ref(v_k_4147_);
    return v_res_4148_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(
    mut v_init_4152_: *mut leanh::LeanObject,
    mut v_x_4153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u8 = 0;
    let mut v_n_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4171_: u8 = 0;
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut v_a_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut v_a_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4153_) == 0 {
                    v_k_4154_ = leanh::lean_ctor_get(v_x_4153_, 1);
                    leanh::lean_inc(v_k_4154_);
                    v_v_4155_ = leanh::lean_ctor_get(v_x_4153_, 2);
                    leanh::lean_inc(v_v_4155_);
                    v_l_4156_ = leanh::lean_ctor_get(v_x_4153_, 3);
                    leanh::lean_inc(v_l_4156_);
                    v_r_4157_ = leanh::lean_ctor_get(v_x_4153_, 4);
                    leanh::lean_inc(v_r_4157_);
                    leanh::lean_dec_ref_known(v_x_4153_, 5);
                    v___x_4158_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_4152_, v_l_4156_);
                    if leanh::lean_obj_tag(v___x_4158_) == 0 {
                        leanh::lean_dec(v_r_4157_);
                        leanh::lean_dec(v_v_4155_);
                        leanh::lean_dec(v_k_4154_);
                        return v___x_4158_;
                    } else {
                        v_a_4159_ = leanh::lean_ctor_get(v___x_4158_, 0);
                        v_isSharedCheck_4199_ =
                            (!leanh::lean_is_exclusive(v___x_4158_)) as u8;
                        if v_isSharedCheck_4199_ == 0 {
                            v___x_4161_ = v___x_4158_;
                            v_isShared_4162_ = v_isSharedCheck_4199_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4159_);
                            leanh::lean_dec(v___x_4158_);
                            v___x_4161_ = leanh::lean_box(0);
                            v_isShared_4162_ = v_isSharedCheck_4199_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_4200_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4200_, 0, v_init_4152_);
                    return v___x_4200_;
                }
            }
            1 => {
                v___x_4163_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0;
                v___x_4164_ = lean_string_dec_eq(v_k_4154_, v___x_4163_);
                if v___x_4164_ == 0 {
                    leanh::lean_inc(v_k_4154_);
                    v_n_4165_ = l_String_toName(v_k_4154_);
                    v___x_4166_ = l_Lean_Name_isAnonymous(v_n_4165_);
                    if v___x_4166_ == 0 {
                        leanh::lean_del_object(v___x_4161_);
                        leanh::lean_dec(v_k_4154_);
                        v___x_4167_ = l_Lean_Json_getStr_x3f(v_v_4155_);
                        if leanh::lean_obj_tag(v___x_4167_) == 0 {
                            leanh::lean_dec(v_n_4165_);
                            leanh::lean_dec(v_a_4159_);
                            leanh::lean_dec(v_r_4157_);
                            v_a_4168_ = leanh::lean_ctor_get(v___x_4167_, 0);
                            v_isSharedCheck_4175_ =
                                (!leanh::lean_is_exclusive(v___x_4167_)) as u8;
                            if v_isSharedCheck_4175_ == 0 {
                                v___x_4170_ = v___x_4167_;
                                v_isShared_4171_ = v_isSharedCheck_4175_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4168_);
                                leanh::lean_dec(v___x_4167_);
                                v___x_4170_ = leanh::lean_box(0);
                                v_isShared_4171_ = v_isSharedCheck_4175_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_4176_ = leanh::lean_ctor_get(v___x_4167_, 0);
                            leanh::lean_inc(v_a_4176_);
                            leanh::lean_dec_ref_known(v___x_4167_, 1);
                            v___x_4177_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_4165_, v_a_4176_, v_a_4159_);
                            v_init_4152_ = v___x_4177_;
                            v_x_4153_ = v_r_4157_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_n_4165_);
                        leanh::lean_dec(v_a_4159_);
                        leanh::lean_dec(v_r_4157_);
                        leanh::lean_dec(v_v_4155_);
                        v___x_4179_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1;
                        v___x_4180_ = lean_string_append(v___x_4179_, v_k_4154_);
                        leanh::lean_dec(v_k_4154_);
                        v___x_4181_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2;
                        v___x_4182_ = lean_string_append(v___x_4180_, v___x_4181_);
                        if v_isShared_4162_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4161_, 0);
                            leanh::lean_ctor_set(v___x_4161_, 0, v___x_4182_);
                            v___x_4184_ = v___x_4161_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4185_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4182_);
                            v___x_4184_ = v_reuseFailAlloc_4185_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4161_);
                    leanh::lean_dec(v_k_4154_);
                    v___x_4186_ = l_Lean_Json_getStr_x3f(v_v_4155_);
                    if leanh::lean_obj_tag(v___x_4186_) == 0 {
                        leanh::lean_dec(v_a_4159_);
                        leanh::lean_dec(v_r_4157_);
                        v_a_4187_ = leanh::lean_ctor_get(v___x_4186_, 0);
                        v_isSharedCheck_4194_ =
                            (!leanh::lean_is_exclusive(v___x_4186_)) as u8;
                        if v_isSharedCheck_4194_ == 0 {
                            v___x_4189_ = v___x_4186_;
                            v_isShared_4190_ = v_isSharedCheck_4194_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4187_);
                            leanh::lean_dec(v___x_4186_);
                            v___x_4189_ = leanh::lean_box(0);
                            v_isShared_4190_ = v_isSharedCheck_4194_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4195_ = leanh::lean_ctor_get(v___x_4186_, 0);
                        leanh::lean_inc(v_a_4195_);
                        leanh::lean_dec_ref_known(v___x_4186_, 1);
                        v___x_4196_ = leanh::lean_box(0);
                        v___x_4197_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4196_, v_a_4195_, v_a_4159_);
                        v_init_4152_ = v___x_4197_;
                        v_x_4153_ = v_r_4157_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4171_ == 0 {
                    v___x_4173_ = v___x_4170_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
                    v___x_4173_ = v_reuseFailAlloc_4174_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4173_;
            }
            4 => {
                return v___x_4184_;
            }
            5 => {
                if v_isShared_4190_ == 0 {
                    v___x_4192_ = v___x_4189_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
                    v___x_4192_ = v_reuseFailAlloc_4193_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(
    mut v_x_4202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4202_) == 5 {
        let mut v_kvPairs_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_kvPairs_4203_ = leanh::lean_ctor_get(v_x_4202_, 0);
        leanh::lean_inc(v_kvPairs_4203_);
        leanh::lean_dec_ref_known(v_x_4202_, 1);
        v___x_4204_ = leanh::lean_box(1);
        v___x_4205_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_4204_, v_kvPairs_4203_);
        return v___x_4205_;
    } else {
        let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4206_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0;
        v___x_4207_ = leanh::lean_unsigned_to_nat(80);
        v___x_4208_ = l_Lean_Json_pretty(v_x_4202_, v___x_4207_);
        v___x_4209_ = lean_string_append(v___x_4206_, v___x_4208_);
        leanh::lean_dec_ref(v___x_4208_);
        v___x_4210_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2;
        v___x_4211_ = lean_string_append(v___x_4209_, v___x_4210_);
        v___x_4212_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4212_, 0, v___x_4211_);
        return v___x_4212_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(
    mut v_j_4213_: *mut leanh::LeanObject,
    mut v_k_4214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4215_ = l_Lean_Json_getObjValD(v_j_4213_, v_k_4214_);
    v___x_4216_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_4215_);
    return v___x_4216_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(
    mut v_j_4217_: *mut leanh::LeanObject,
    mut v_k_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4219_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_4217_, v_k_4218_);
    leanh::lean_dec_ref(v_k_4218_);
    return v_res_4219_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4248_: u8 = 0;
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4248_ = 1;
    v___x_4249_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11;
    v___x_4250_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4249_, v___x_4248_);
    return v___x_4250_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4252_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13;
    v___x_4253_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
    v___x_4254_ = lean_string_append(v___x_4253_, v___x_4252_);
    return v___x_4254_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4257_ = 1;
    v___x_4258_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15;
    v___x_4259_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4258_, v___x_4257_);
    return v___x_4259_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4260_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
    v___x_4261_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
    v___x_4262_ = lean_string_append(v___x_4261_, v___x_4260_);
    return v___x_4262_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4264_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18;
    v___x_4265_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
    v___x_4266_ = lean_string_append(v___x_4265_, v___x_4264_);
    return v___x_4266_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_4269_: u8 = 0;
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = 1;
    v___x_4270_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20;
    v___x_4271_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4270_, v___x_4269_);
    return v___x_4271_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4272_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
    v___x_4273_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
    v___x_4274_ = lean_string_append(v___x_4273_, v___x_4272_);
    return v___x_4274_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4275_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18;
    v___x_4276_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
    v___x_4277_ = lean_string_append(v___x_4276_, v___x_4275_);
    return v___x_4277_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4280_ = 1;
    v___x_4281_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24;
    v___x_4282_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4281_, v___x_4280_);
    return v___x_4282_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4283_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
    v___x_4284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
    v___x_4285_ = lean_string_append(v___x_4284_, v___x_4283_);
    return v___x_4285_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18;
    v___x_4287_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
    v___x_4288_ = lean_string_append(v___x_4287_, v___x_4286_);
    return v___x_4288_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_4291_: u8 = 0;
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = 1;
    v___x_4292_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28;
    v___x_4293_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4292_, v___x_4291_);
    return v___x_4293_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
    v___x_4295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
    v___x_4296_ = lean_string_append(v___x_4295_, v___x_4294_);
    return v___x_4296_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18;
    v___x_4298_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
    v___x_4299_ = lean_string_append(v___x_4298_, v___x_4297_);
    return v___x_4299_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_4302_: u8 = 0;
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4302_ = 1;
    v___x_4303_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32;
    v___x_4304_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4303_, v___x_4302_);
    return v___x_4304_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4305_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
    v___x_4306_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
    v___x_4307_ = lean_string_append(v___x_4306_, v___x_4305_);
    return v___x_4307_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18;
    v___x_4309_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
    v___x_4310_ = lean_string_append(v___x_4309_, v___x_4308_);
    return v___x_4310_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_4313_: u8 = 0;
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4313_ = 1;
    v___x_4314_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36;
    v___x_4315_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4314_, v___x_4313_);
    return v___x_4315_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4316_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
    v___x_4317_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
    v___x_4318_ = lean_string_append(v___x_4317_, v___x_4316_);
    return v___x_4318_;
}
pub unsafe fn _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4319_ =
        l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18;
    v___x_4320_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
    v___x_4321_ = lean_string_append(v___x_4320_, v___x_4319_);
    return v___x_4321_;
}
pub unsafe fn l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(
    mut v_json_4322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4328_: u8 = 0;
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4334_: u8 = 0;
    let mut v_a_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4342_: u8 = 0;
    let mut v_a_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_a_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4363_: u8 = 0;
    let mut v_a_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4370_: u8 = 0;
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_a_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_a_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v_a_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4401_: u8 = 0;
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_a_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4418_: u8 = 0;
    let mut v_a_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_a_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4439_: u8 = 0;
    let mut v_a_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4443_: u8 = 0;
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4447_: u8 = 0;
    let mut v_a_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: u64 = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4323_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0;
                leanh::lean_inc(v_json_4322_);
                v___x_4324_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_4322_, v___x_4323_);
                if leanh::lean_obj_tag(v___x_4324_) == 0 {
                    leanh::lean_dec(v_json_4322_);
                    v_a_4325_ = leanh::lean_ctor_get(v___x_4324_, 0);
                    v_isSharedCheck_4334_ = (!leanh::lean_is_exclusive(v___x_4324_)) as u8;
                    if v_isSharedCheck_4334_ == 0 {
                        v___x_4327_ = v___x_4324_;
                        v_isShared_4328_ = v_isSharedCheck_4334_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4325_);
                        leanh::lean_dec(v___x_4324_);
                        v___x_4327_ = leanh::lean_box(0);
                        v_isShared_4328_ = v_isSharedCheck_4334_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_4324_) == 0 {
                        leanh::lean_dec(v_json_4322_);
                        v_a_4335_ = leanh::lean_ctor_get(v___x_4324_, 0);
                        v_isSharedCheck_4342_ =
                            (!leanh::lean_is_exclusive(v___x_4324_)) as u8;
                        if v_isSharedCheck_4342_ == 0 {
                            v___x_4337_ = v___x_4324_;
                            v_isShared_4338_ = v_isSharedCheck_4342_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4335_);
                            leanh::lean_dec(v___x_4324_);
                            v___x_4337_ = leanh::lean_box(0);
                            v_isShared_4338_ = v_isSharedCheck_4342_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4343_ = leanh::lean_ctor_get(v___x_4324_, 0);
                        leanh::lean_inc(v_a_4343_);
                        leanh::lean_dec_ref_known(v___x_4324_, 1);
                        v___x_4344_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1;
                        leanh::lean_inc(v_json_4322_);
                        v___x_4345_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_4322_, v___x_4344_);
                        if leanh::lean_obj_tag(v___x_4345_) == 0 {
                            leanh::lean_dec(v_a_4343_);
                            leanh::lean_dec(v_json_4322_);
                            v_a_4346_ = leanh::lean_ctor_get(v___x_4345_, 0);
                            v_isSharedCheck_4355_ =
                                (!leanh::lean_is_exclusive(v___x_4345_)) as u8;
                            if v_isSharedCheck_4355_ == 0 {
                                v___x_4348_ = v___x_4345_;
                                v_isShared_4349_ = v_isSharedCheck_4355_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4346_);
                                leanh::lean_dec(v___x_4345_);
                                v___x_4348_ = leanh::lean_box(0);
                                v_isShared_4349_ = v_isSharedCheck_4355_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_4345_) == 0 {
                                leanh::lean_dec(v_a_4343_);
                                leanh::lean_dec(v_json_4322_);
                                v_a_4356_ = leanh::lean_ctor_get(v___x_4345_, 0);
                                v_isSharedCheck_4363_ =
                                    (!leanh::lean_is_exclusive(v___x_4345_)) as u8;
                                if v_isSharedCheck_4363_ == 0 {
                                    v___x_4358_ = v___x_4345_;
                                    v_isShared_4359_ = v_isSharedCheck_4363_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4356_);
                                    leanh::lean_dec(v___x_4345_);
                                    v___x_4358_ = leanh::lean_box(0);
                                    v_isShared_4359_ = v_isSharedCheck_4363_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4364_ = leanh::lean_ctor_get(v___x_4345_, 0);
                                leanh::lean_inc(v_a_4364_);
                                leanh::lean_dec_ref_known(v___x_4345_, 1);
                                v___x_4365_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2;
                                leanh::lean_inc(v_json_4322_);
                                v___x_4366_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_4322_, v___x_4365_);
                                if leanh::lean_obj_tag(v___x_4366_) == 0 {
                                    leanh::lean_dec(v_a_4364_);
                                    leanh::lean_dec(v_a_4343_);
                                    leanh::lean_dec(v_json_4322_);
                                    v_a_4367_ = leanh::lean_ctor_get(v___x_4366_, 0);
                                    v_isSharedCheck_4376_ =
                                        (!leanh::lean_is_exclusive(v___x_4366_)) as u8;
                                    if v_isSharedCheck_4376_ == 0 {
                                        v___x_4369_ = v___x_4366_;
                                        v_isShared_4370_ = v_isSharedCheck_4376_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4367_);
                                        leanh::lean_dec(v___x_4366_);
                                        v___x_4369_ = leanh::lean_box(0);
                                        v_isShared_4370_ = v_isSharedCheck_4376_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_4366_) == 0 {
                                        leanh::lean_dec(v_a_4364_);
                                        leanh::lean_dec(v_a_4343_);
                                        leanh::lean_dec(v_json_4322_);
                                        v_a_4377_ = leanh::lean_ctor_get(v___x_4366_, 0);
                                        v_isSharedCheck_4384_ =
                                            (!leanh::lean_is_exclusive(v___x_4366_)) as u8;
                                        if v_isSharedCheck_4384_ == 0 {
                                            v___x_4379_ = v___x_4366_;
                                            v_isShared_4380_ = v_isSharedCheck_4384_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4377_);
                                            leanh::lean_dec(v___x_4366_);
                                            v___x_4379_ = leanh::lean_box(0);
                                            v_isShared_4380_ = v_isSharedCheck_4384_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4385_ = leanh::lean_ctor_get(v___x_4366_, 0);
                                        leanh::lean_inc(v_a_4385_);
                                        leanh::lean_dec_ref_known(v___x_4366_, 1);
                                        v___x_4386_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3;
                                        leanh::lean_inc(v_json_4322_);
                                        v___x_4387_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_4322_, v___x_4386_);
                                        if leanh::lean_obj_tag(v___x_4387_) == 0 {
                                            leanh::lean_dec(v_a_4385_);
                                            leanh::lean_dec(v_a_4364_);
                                            leanh::lean_dec(v_a_4343_);
                                            leanh::lean_dec(v_json_4322_);
                                            v_a_4388_ = leanh::lean_ctor_get(v___x_4387_, 0);
                                            v_isSharedCheck_4397_ =
                                                (!leanh::lean_is_exclusive(v___x_4387_))
                                                    as u8;
                                            if v_isSharedCheck_4397_ == 0 {
                                                v___x_4390_ = v___x_4387_;
                                                v_isShared_4391_ = v_isSharedCheck_4397_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4388_);
                                                leanh::lean_dec(v___x_4387_);
                                                v___x_4390_ = leanh::lean_box(0);
                                                v_isShared_4391_ = v_isSharedCheck_4397_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_4387_) == 0 {
                                                leanh::lean_dec(v_a_4385_);
                                                leanh::lean_dec(v_a_4364_);
                                                leanh::lean_dec(v_a_4343_);
                                                leanh::lean_dec(v_json_4322_);
                                                v_a_4398_ =
                                                    leanh::lean_ctor_get(v___x_4387_, 0);
                                                v_isSharedCheck_4405_ =
                                                    (!leanh::lean_is_exclusive(v___x_4387_))
                                                        as u8;
                                                if v_isSharedCheck_4405_ == 0 {
                                                    v___x_4400_ = v___x_4387_;
                                                    v_isShared_4401_ = v_isSharedCheck_4405_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4398_);
                                                    leanh::lean_dec(v___x_4387_);
                                                    v___x_4400_ = leanh::lean_box(0);
                                                    v_isShared_4401_ = v_isSharedCheck_4405_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_4406_ =
                                                    leanh::lean_ctor_get(v___x_4387_, 0);
                                                leanh::lean_inc(v_a_4406_);
                                                leanh::lean_dec_ref_known(v___x_4387_, 1);
                                                v___x_4407_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4;
                                                leanh::lean_inc(v_json_4322_);
                                                v___x_4408_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_4322_, v___x_4407_);
                                                if leanh::lean_obj_tag(v___x_4408_) == 0 {
                                                    leanh::lean_dec(v_a_4406_);
                                                    leanh::lean_dec(v_a_4385_);
                                                    leanh::lean_dec(v_a_4364_);
                                                    leanh::lean_dec(v_a_4343_);
                                                    leanh::lean_dec(v_json_4322_);
                                                    v_a_4409_ =
                                                        leanh::lean_ctor_get(v___x_4408_, 0);
                                                    v_isSharedCheck_4418_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4408_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4418_ == 0 {
                                                        v___x_4411_ = v___x_4408_;
                                                        v_isShared_4412_ = v_isSharedCheck_4418_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4409_);
                                                        leanh::lean_dec(v___x_4408_);
                                                        v___x_4411_ = leanh::lean_box(0);
                                                        v_isShared_4412_ = v_isSharedCheck_4418_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_4408_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_4406_);
                                                        leanh::lean_dec(v_a_4385_);
                                                        leanh::lean_dec(v_a_4364_);
                                                        leanh::lean_dec(v_a_4343_);
                                                        leanh::lean_dec(v_json_4322_);
                                                        v_a_4419_ = leanh::lean_ctor_get(
                                                            v___x_4408_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4426_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_4408_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4426_ == 0 {
                                                            v___x_4421_ = v___x_4408_;
                                                            v_isShared_4422_ =
                                                                v_isSharedCheck_4426_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_4419_);
                                                            leanh::lean_dec(v___x_4408_);
                                                            v___x_4421_ = leanh::lean_box(0);
                                                            v_isShared_4422_ =
                                                                v_isSharedCheck_4426_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_4427_ = leanh::lean_ctor_get(
                                                            v___x_4408_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_4427_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_4408_,
                                                            1,
                                                        );
                                                        v___x_4428_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5;
                                                        v___x_4429_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_4322_, v___x_4428_);
                                                        if leanh::lean_obj_tag(v___x_4429_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec(v_a_4427_);
                                                            leanh::lean_dec(v_a_4406_);
                                                            leanh::lean_dec(v_a_4385_);
                                                            leanh::lean_dec(v_a_4364_);
                                                            leanh::lean_dec(v_a_4343_);
                                                            v_a_4430_ = leanh::lean_ctor_get(
                                                                v___x_4429_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4439_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_4429_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4439_ == 0 {
                                                                v___x_4432_ = v___x_4429_;
                                                                v_isShared_4433_ =
                                                                    v_isSharedCheck_4439_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_4430_);
                                                                leanh::lean_dec(v___x_4429_);
                                                                v___x_4432_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_4433_ =
                                                                    v_isSharedCheck_4439_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v___x_4429_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec(v_a_4427_);
                                                                leanh::lean_dec(v_a_4406_);
                                                                leanh::lean_dec(v_a_4385_);
                                                                leanh::lean_dec(v_a_4364_);
                                                                leanh::lean_dec(v_a_4343_);
                                                                v_a_4440_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_4429_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_4447_ = (!leanh::lean_is_exclusive(v___x_4429_)) as u8;
                                                                if v_isSharedCheck_4447_ == 0 {
                                                                    v___x_4442_ = v___x_4429_;
                                                                    v_isShared_4443_ =
                                                                        v_isSharedCheck_4447_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_4440_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_4429_,
                                                                    );
                                                                    v___x_4442_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_4443_ =
                                                                        v_isSharedCheck_4447_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_4448_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_4429_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_4457_ = (!leanh::lean_is_exclusive(v___x_4429_)) as u8;
                                                                if v_isSharedCheck_4457_ == 0 {
                                                                    v___x_4450_ = v___x_4429_;
                                                                    v_isShared_4451_ =
                                                                        v_isSharedCheck_4457_;
                                                                    state = 25;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_4448_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_4429_,
                                                                    );
                                                                    v___x_4450_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_4451_ =
                                                                        v_isSharedCheck_4457_;
                                                                    state = 25;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4329_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
                v___x_4330_ = lean_string_append(v___x_4329_, v_a_4325_);
                leanh::lean_dec(v_a_4325_);
                if v_isShared_4328_ == 0 {
                    leanh::lean_ctor_set(v___x_4327_, 0, v___x_4330_);
                    v___x_4332_ = v___x_4327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4330_);
                    v___x_4332_ = v_reuseFailAlloc_4333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4332_;
            }
            3 => {
                if v_isShared_4338_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4337_, 0);
                    v___x_4340_ = v___x_4337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4341_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
                    v___x_4340_ = v_reuseFailAlloc_4341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4340_;
            }
            5 => {
                v___x_4350_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
                v___x_4351_ = lean_string_append(v___x_4350_, v_a_4346_);
                leanh::lean_dec(v_a_4346_);
                if v_isShared_4349_ == 0 {
                    leanh::lean_ctor_set(v___x_4348_, 0, v___x_4351_);
                    v___x_4353_ = v___x_4348_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4351_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4353_;
            }
            7 => {
                if v_isShared_4359_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4358_, 0);
                    v___x_4361_ = v___x_4358_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
                    v___x_4361_ = v_reuseFailAlloc_4362_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4361_;
            }
            9 => {
                v___x_4371_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
                v___x_4372_ = lean_string_append(v___x_4371_, v_a_4367_);
                leanh::lean_dec(v_a_4367_);
                if v_isShared_4370_ == 0 {
                    leanh::lean_ctor_set(v___x_4369_, 0, v___x_4372_);
                    v___x_4374_ = v___x_4369_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4372_);
                    v___x_4374_ = v_reuseFailAlloc_4375_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4374_;
            }
            11 => {
                if v_isShared_4380_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4379_, 0);
                    v___x_4382_ = v___x_4379_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
                    v___x_4382_ = v_reuseFailAlloc_4383_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4382_;
            }
            13 => {
                v___x_4392_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
                v___x_4393_ = lean_string_append(v___x_4392_, v_a_4388_);
                leanh::lean_dec(v_a_4388_);
                if v_isShared_4391_ == 0 {
                    leanh::lean_ctor_set(v___x_4390_, 0, v___x_4393_);
                    v___x_4395_ = v___x_4390_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4395_;
            }
            15 => {
                if v_isShared_4401_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4400_, 0);
                    v___x_4403_ = v___x_4400_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
                    v___x_4403_ = v_reuseFailAlloc_4404_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4403_;
            }
            17 => {
                v___x_4413_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
                v___x_4414_ = lean_string_append(v___x_4413_, v_a_4409_);
                leanh::lean_dec(v_a_4409_);
                if v_isShared_4412_ == 0 {
                    leanh::lean_ctor_set(v___x_4411_, 0, v___x_4414_);
                    v___x_4416_ = v___x_4411_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4417_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4414_);
                    v___x_4416_ = v_reuseFailAlloc_4417_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4416_;
            }
            19 => {
                if v_isShared_4422_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4421_, 0);
                    v___x_4424_ = v___x_4421_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
                    v___x_4424_ = v_reuseFailAlloc_4425_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4424_;
            }
            21 => {
                v___x_4434_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39), core::ptr::addr_of_mut!(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once), _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
                v___x_4435_ = lean_string_append(v___x_4434_, v_a_4430_);
                leanh::lean_dec(v_a_4430_);
                if v_isShared_4433_ == 0 {
                    leanh::lean_ctor_set(v___x_4432_, 0, v___x_4435_);
                    v___x_4437_ = v___x_4432_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4438_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
                    v___x_4437_ = v_reuseFailAlloc_4438_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4437_;
            }
            23 => {
                if v_isShared_4443_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4442_, 0);
                    v___x_4445_ = v___x_4442_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
                    v___x_4445_ = v_reuseFailAlloc_4446_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4445_;
            }
            25 => {
                v___x_4452_ = leanh::lean_alloc_ctor(0, 5, (8) as u32);
                leanh::lean_ctor_set(v___x_4452_, 0, v_a_4343_);
                leanh::lean_ctor_set(v___x_4452_, 1, v_a_4364_);
                leanh::lean_ctor_set(v___x_4452_, 2, v_a_4385_);
                leanh::lean_ctor_set(v___x_4452_, 3, v_a_4406_);
                leanh::lean_ctor_set(v___x_4452_, 4, v_a_4448_);
                v___x_4453_ = leanh::lean_unbox_uint64(v_a_4427_);
                leanh::lean_dec(v_a_4427_);
                leanh::lean_ctor_set_uint64(
                    v___x_4452_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_4453_,
                );
                if v_isShared_4451_ == 0 {
                    leanh::lean_ctor_set(v___x_4450_, 0, v___x_4452_);
                    v___x_4455_ = v___x_4450_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4452_);
                    v___x_4455_ = v_reuseFailAlloc_4456_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_importConfigFile___lam__0___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4461_ = l_Lake_importConfigFile___lam__0___closed__0;
    v___x_4462_ = lean_mk_io_user_error(v___x_4461_);
    return v___x_4462_;
}
pub unsafe fn l_Lake_importConfigFile___lam__0(
    mut v___x_4463_: *mut leanh::LeanObject,
    mut v___x_4464_: *mut leanh::LeanObject,
    mut v_h_4465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: u8 = 0;
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: u8 = 0;
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4482_: u8 = 0;
    let mut v_unused_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4487_: u8 = 0;
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4491_: u8 = 0;
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_unused_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_a_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4521_: u8 = 0;
    let mut v_a_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_a_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4467_ = 1;
                v___x_4468_ = lean_io_prim_handle_mk(v___x_4463_, v___x_4467_);
                if leanh::lean_obj_tag(v___x_4468_) == 0 {
                    v_a_4469_ = leanh::lean_ctor_get(v___x_4468_, 0);
                    leanh::lean_inc(v_a_4469_);
                    leanh::lean_dec_ref_known(v___x_4468_, 1);
                    v___x_4470_ = 1;
                    v___x_4471_ = lean_io_prim_handle_try_lock(v_a_4469_, v___x_4470_);
                    if leanh::lean_obj_tag(v___x_4471_) == 0 {
                        v_a_4472_ = leanh::lean_ctor_get(v___x_4471_, 0);
                        leanh::lean_inc(v_a_4472_);
                        leanh::lean_dec_ref_known(v___x_4471_, 1);
                        v___x_4473_ = (leanh::lean_unbox(v_a_4472_) as u8);
                        leanh::lean_dec(v_a_4472_);
                        if v___x_4473_ == 0 {
                            leanh::lean_dec(v_a_4469_);
                            v___x_4474_ = lean_io_prim_handle_unlock(v_h_4465_);
                            if leanh::lean_obj_tag(v___x_4474_) == 0 {
                                v_isSharedCheck_4482_ =
                                    (!leanh::lean_is_exclusive(v___x_4474_)) as u8;
                                if v_isSharedCheck_4482_ == 0 {
                                    v_unused_4483_ = leanh::lean_ctor_get(v___x_4474_, 0);
                                    leanh::lean_dec(v_unused_4483_);
                                    v___x_4476_ = v___x_4474_;
                                    v_isShared_4477_ = v_isSharedCheck_4482_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_4474_);
                                    v___x_4476_ = leanh::lean_box(0);
                                    v_isShared_4477_ = v_isSharedCheck_4482_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_4484_ = leanh::lean_ctor_get(v___x_4474_, 0);
                                v_isSharedCheck_4491_ =
                                    (!leanh::lean_is_exclusive(v___x_4474_)) as u8;
                                if v_isSharedCheck_4491_ == 0 {
                                    v___x_4486_ = v___x_4474_;
                                    v_isShared_4487_ = v_isSharedCheck_4491_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4484_);
                                    leanh::lean_dec(v___x_4474_);
                                    v___x_4486_ = leanh::lean_box(0);
                                    v_isShared_4487_ = v_isSharedCheck_4491_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4492_ = lean_io_prim_handle_unlock(v_h_4465_);
                            if leanh::lean_obj_tag(v___x_4492_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4492_, 1);
                                v___x_4493_ = 3;
                                v___x_4494_ = lean_io_prim_handle_mk(v___x_4464_, v___x_4493_);
                                if leanh::lean_obj_tag(v___x_4494_) == 0 {
                                    v_a_4495_ = leanh::lean_ctor_get(v___x_4494_, 0);
                                    leanh::lean_inc(v_a_4495_);
                                    leanh::lean_dec_ref_known(v___x_4494_, 1);
                                    v___x_4496_ = lean_io_prim_handle_lock(v_a_4495_, v___x_4470_);
                                    if leanh::lean_obj_tag(v___x_4496_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4496_, 1);
                                        v___x_4497_ = lean_io_prim_handle_unlock(v_a_4469_);
                                        leanh::lean_dec(v_a_4469_);
                                        if leanh::lean_obj_tag(v___x_4497_) == 0 {
                                            v_isSharedCheck_4504_ =
                                                (!leanh::lean_is_exclusive(v___x_4497_))
                                                    as u8;
                                            if v_isSharedCheck_4504_ == 0 {
                                                v_unused_4505_ =
                                                    leanh::lean_ctor_get(v___x_4497_, 0);
                                                leanh::lean_dec(v_unused_4505_);
                                                v___x_4499_ = v___x_4497_;
                                                v_isShared_4500_ = v_isSharedCheck_4504_;
                                                state = 5;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___x_4497_);
                                                v___x_4499_ = leanh::lean_box(0);
                                                v_isShared_4500_ = v_isSharedCheck_4504_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_4495_);
                                            v_a_4506_ = leanh::lean_ctor_get(v___x_4497_, 0);
                                            v_isSharedCheck_4513_ =
                                                (!leanh::lean_is_exclusive(v___x_4497_))
                                                    as u8;
                                            if v_isSharedCheck_4513_ == 0 {
                                                v___x_4508_ = v___x_4497_;
                                                v_isShared_4509_ = v_isSharedCheck_4513_;
                                                state = 7;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4506_);
                                                leanh::lean_dec(v___x_4497_);
                                                v___x_4508_ = leanh::lean_box(0);
                                                v_isShared_4509_ = v_isSharedCheck_4513_;
                                                state = 7;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_4495_);
                                        leanh::lean_dec(v_a_4469_);
                                        v_a_4514_ = leanh::lean_ctor_get(v___x_4496_, 0);
                                        v_isSharedCheck_4521_ =
                                            (!leanh::lean_is_exclusive(v___x_4496_)) as u8;
                                        if v_isSharedCheck_4521_ == 0 {
                                            v___x_4516_ = v___x_4496_;
                                            v_isShared_4517_ = v_isSharedCheck_4521_;
                                            state = 9;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4514_);
                                            leanh::lean_dec(v___x_4496_);
                                            v___x_4516_ = leanh::lean_box(0);
                                            v_isShared_4517_ = v_isSharedCheck_4521_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4469_);
                                    return v___x_4494_;
                                }
                            } else {
                                leanh::lean_dec(v_a_4469_);
                                v_a_4522_ = leanh::lean_ctor_get(v___x_4492_, 0);
                                v_isSharedCheck_4529_ =
                                    (!leanh::lean_is_exclusive(v___x_4492_)) as u8;
                                if v_isSharedCheck_4529_ == 0 {
                                    v___x_4524_ = v___x_4492_;
                                    v_isShared_4525_ = v_isSharedCheck_4529_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4522_);
                                    leanh::lean_dec(v___x_4492_);
                                    v___x_4524_ = leanh::lean_box(0);
                                    v_isShared_4525_ = v_isSharedCheck_4529_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4469_);
                        v_a_4530_ = leanh::lean_ctor_get(v___x_4471_, 0);
                        v_isSharedCheck_4537_ =
                            (!leanh::lean_is_exclusive(v___x_4471_)) as u8;
                        if v_isSharedCheck_4537_ == 0 {
                            v___x_4532_ = v___x_4471_;
                            v_isShared_4533_ = v_isSharedCheck_4537_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4530_);
                            leanh::lean_dec(v___x_4471_);
                            v___x_4532_ = leanh::lean_box(0);
                            v_isShared_4533_ = v_isSharedCheck_4537_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    return v___x_4468_;
                }
            }
            1 => {
                v___x_4478_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_importConfigFile___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_importConfigFile___lam__0___closed__1_once),
                    _init_l_Lake_importConfigFile___lam__0___closed__1,
                );
                if v_isShared_4477_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4476_, 1);
                    leanh::lean_ctor_set(v___x_4476_, 0, v___x_4478_);
                    v___x_4480_ = v___x_4476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4478_);
                    v___x_4480_ = v_reuseFailAlloc_4481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4480_;
            }
            3 => {
                if v_isShared_4487_ == 0 {
                    v___x_4489_ = v___x_4486_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4490_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
                    v___x_4489_ = v_reuseFailAlloc_4490_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4489_;
            }
            5 => {
                if v_isShared_4500_ == 0 {
                    leanh::lean_ctor_set(v___x_4499_, 0, v_a_4495_);
                    v___x_4502_ = v___x_4499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4495_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4502_;
            }
            7 => {
                if v_isShared_4509_ == 0 {
                    v___x_4511_ = v___x_4508_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
                    v___x_4511_ = v_reuseFailAlloc_4512_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4511_;
            }
            9 => {
                if v_isShared_4517_ == 0 {
                    v___x_4519_ = v___x_4516_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4520_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
                    v___x_4519_ = v_reuseFailAlloc_4520_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4519_;
            }
            11 => {
                if v_isShared_4525_ == 0 {
                    v___x_4527_ = v___x_4524_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
                    v___x_4527_ = v_reuseFailAlloc_4528_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4527_;
            }
            13 => {
                if v_isShared_4533_ == 0 {
                    v___x_4535_ = v___x_4532_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
                    v___x_4535_ = v_reuseFailAlloc_4536_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_importConfigFile___lam__0___boxed(
    mut v___x_4538_: *mut leanh::LeanObject,
    mut v___x_4539_: *mut leanh::LeanObject,
    mut v_h_4540_: *mut leanh::LeanObject,
    mut v___y_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_Lake_importConfigFile___lam__0(v___x_4538_, v___x_4539_, v_h_4540_);
    leanh::lean_dec(v_h_4540_);
    leanh::lean_dec_ref(v___x_4539_);
    leanh::lean_dec_ref(v___x_4538_);
    return v_res_4542_;
}
pub unsafe fn l_Lake_importConfigFile(
    mut v_cfg_4555_: *mut leanh::LeanObject,
    mut v_a_4556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: u8 = 0;
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wsDir_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgIdx_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgName_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeOpts_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reconfigure_4578_: u8 = 0;
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_configDir_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeOpts_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u64 = 0;
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: u8 = 0;
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v_a_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: u8 = 0;
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_unused_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4637_: u8 = 0;
    let mut v_a_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4647_: u8 = 0;
    let mut v_unused_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: u8 = 0;
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: u64 = 0;
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v_a_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: u8 = 0;
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_unused_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4697_: u8 = 0;
    let mut v_a_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4707_: u8 = 0;
    let mut v_unused_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: u8 = 0;
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: u8 = 0;
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: u8 = 0;
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: u8 = 0;
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: u8 = 0;
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: u8 = 0;
    let mut v_idx_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_platform_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanHash_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_configHash_4793_: u64 = 0;
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: u8 = 0;
    let mut v___x_4796_: u64 = 0;
    let mut v___x_4797_: u8 = 0;
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: u8 = 0;
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: u8 = 0;
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: u8 = 0;
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: u8 = 0;
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: u8 = 0;
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: u8 = 0;
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: u8 = 0;
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: u8 = 0;
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: u8 = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: u8 = 0;
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: u8 = 0;
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: u8 = 0;
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: u8 = 0;
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_4570_ = leanh::lean_ctor_get(v_cfg_4555_, 0);
                leanh::lean_inc_ref(v_lakeEnv_4570_);
                v_wsDir_4571_ = leanh::lean_ctor_get(v_cfg_4555_, 2);
                leanh::lean_inc_ref(v_wsDir_4571_);
                v_pkgIdx_4572_ = leanh::lean_ctor_get(v_cfg_4555_, 3);
                leanh::lean_inc(v_pkgIdx_4572_);
                v_pkgName_4573_ = leanh::lean_ctor_get(v_cfg_4555_, 4);
                leanh::lean_inc(v_pkgName_4573_);
                v_pkgDir_4574_ = leanh::lean_ctor_get(v_cfg_4555_, 6);
                leanh::lean_inc_ref(v_pkgDir_4574_);
                v_configFile_4575_ = leanh::lean_ctor_get(v_cfg_4555_, 8);
                leanh::lean_inc_ref_n(v_configFile_4575_, 2);
                v_lakeOpts_4576_ = leanh::lean_ctor_get(v_cfg_4555_, 12);
                leanh::lean_inc(v_lakeOpts_4576_);
                v_leanOpts_4577_ = leanh::lean_ctor_get(v_cfg_4555_, 13);
                leanh::lean_inc_ref(v_leanOpts_4577_);
                v_reconfigure_4578_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4555_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16) as u32,
                );
                leanh::lean_dec_ref(v_cfg_4555_);
                v___x_4579_ = l_System_FilePath_fileName(v_configFile_4575_);
                if leanh::lean_obj_tag(v___x_4579_) == 0 {
                    leanh::lean_dec_ref(v_leanOpts_4577_);
                    leanh::lean_dec(v_lakeOpts_4576_);
                    leanh::lean_dec_ref(v_configFile_4575_);
                    leanh::lean_dec_ref(v_pkgDir_4574_);
                    leanh::lean_dec(v_pkgName_4573_);
                    leanh::lean_dec(v_pkgIdx_4572_);
                    leanh::lean_dec_ref(v_wsDir_4571_);
                    leanh::lean_dec_ref(v_lakeEnv_4570_);
                    v___x_4580_ = l_Lake_importConfigFile___closed__1;
                    v___x_4581_ = lean_array_get_size(v_a_4556_);
                    v___x_4582_ = lean_array_push(v_a_4556_, v___x_4580_);
                    v___x_4583_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4583_, 0, v___x_4581_);
                    leanh::lean_ctor_set(v___x_4583_, 1, v___x_4582_);
                    return v___x_4583_;
                } else {
                    v_val_4584_ = leanh::lean_ctor_get(v___x_4579_, 0);
                    leanh::lean_inc(v_val_4584_);
                    leanh::lean_dec_ref_known(v___x_4579_, 1);
                    v___x_4585_ = l_Lake_defaultLakeDir;
                    v___x_4586_ = l_Lake_joinRelative(v_wsDir_4571_, v___x_4585_);
                    v___x_4587_ = l_Lake_importConfigFile___closed__2;
                    v___x_4588_ = l_Lake_joinRelative(v___x_4586_, v___x_4587_);
                    leanh::lean_inc(v_pkgIdx_4572_);
                    v___x_4589_ = l_Nat_reprFast(v_pkgIdx_4572_);
                    v_configDir_4590_ = l_Lake_joinRelative(v___x_4588_, v___x_4589_);
                    leanh::lean_inc_ref(v_configDir_4590_);
                    v___x_4591_ = l_IO_FS_createDirAll(v_configDir_4590_);
                    if leanh::lean_obj_tag(v___x_4591_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4591_, 1);
                        v___x_4592_ = l_Lake_computeTextFileHash(v_configFile_4575_);
                        if leanh::lean_obj_tag(v___x_4592_) == 0 {
                            v_a_4593_ = leanh::lean_ctor_get(v___x_4592_, 0);
                            leanh::lean_inc(v_a_4593_);
                            leanh::lean_dec_ref_known(v___x_4592_, 1);
                            v___x_4594_ = l_Lake_importConfigFile___closed__3;
                            leanh::lean_inc_n(v_val_4584_, 2);
                            v___x_4595_ = l_System_FilePath_withExtension(v_val_4584_, v___x_4594_);
                            leanh::lean_inc_ref_n(v_configDir_4590_, 2);
                            v___x_4596_ = l_Lake_joinRelative(v_configDir_4590_, v___x_4595_);
                            v___x_4597_ = l_Lake_importConfigFile___closed__4;
                            v___x_4598_ = l_System_FilePath_withExtension(v_val_4584_, v___x_4597_);
                            v___x_4599_ = l_Lake_joinRelative(v_configDir_4590_, v___x_4598_);
                            v___x_4739_ = l_System_FilePath_pathExists(v___x_4599_);
                            v___x_4740_ = l_Lake_importConfigFile___closed__5;
                            v___x_4741_ = l_System_FilePath_withExtension(v_val_4584_, v___x_4740_);
                            v___x_4742_ = l_Lake_joinRelative(v_configDir_4590_, v___x_4741_);
                            if v___x_4739_ == 0 {
                                leanh::lean_inc_ref(v_pkgDir_4574_);
                                v___x_4843_ = l_Lake_joinRelative(v_pkgDir_4574_, v___x_4585_);
                                v___x_4844_ = l_IO_FS_createDirAll(v___x_4843_);
                                if leanh::lean_obj_tag(v___x_4844_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4844_, 1);
                                    v___x_4845_ = 2;
                                    v___x_4846_ = lean_io_prim_handle_mk(v___x_4599_, v___x_4845_);
                                    if leanh::lean_obj_tag(v___x_4846_) == 0 {
                                        leanh::lean_dec_ref(v___x_4742_);
                                        v_a_4847_ = leanh::lean_ctor_get(v___x_4846_, 0);
                                        leanh::lean_inc(v_a_4847_);
                                        leanh::lean_dec_ref_known(v___x_4846_, 1);
                                        v___x_4848_ = 1;
                                        v___x_4849_ =
                                            lean_io_prim_handle_lock(v_a_4847_, v___x_4848_);
                                        if leanh::lean_obj_tag(v___x_4849_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_4849_, 1);
                                            v_h_4601_ = v_a_4847_;
                                            v_lakeOpts_4602_ = v_lakeOpts_4576_;
                                            v___y_4603_ = v_a_4556_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v_a_4847_);
                                            leanh::lean_dec_ref(v___x_4599_);
                                            leanh::lean_dec_ref(v___x_4596_);
                                            leanh::lean_dec(v_a_4593_);
                                            leanh::lean_dec_ref(v_leanOpts_4577_);
                                            leanh::lean_dec(v_lakeOpts_4576_);
                                            leanh::lean_dec_ref(v_configFile_4575_);
                                            leanh::lean_dec_ref(v_pkgDir_4574_);
                                            leanh::lean_dec(v_pkgName_4573_);
                                            leanh::lean_dec(v_pkgIdx_4572_);
                                            leanh::lean_dec_ref(v_lakeEnv_4570_);
                                            v_a_4850_ = leanh::lean_ctor_get(v___x_4849_, 0);
                                            leanh::lean_inc(v_a_4850_);
                                            leanh::lean_dec_ref_known(v___x_4849_, 1);
                                            v___x_4851_ = lean_io_error_to_string(v_a_4850_);
                                            v___x_4852_ = 3;
                                            v___x_4853_ =
                                                leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_4853_,
                                                0,
                                                v___x_4851_,
                                            );
                                            leanh::lean_ctor_set_uint8(
                                                v___x_4853_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 1)
                                                    as u32,
                                                v___x_4852_,
                                            );
                                            v___x_4854_ = lean_array_get_size(v_a_4556_);
                                            v___x_4855_ = lean_array_push(v_a_4556_, v___x_4853_);
                                            v___x_4856_ =
                                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_4856_,
                                                0,
                                                v___x_4854_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_4856_,
                                                1,
                                                v___x_4855_,
                                            );
                                            return v___x_4856_;
                                        }
                                    } else {
                                        v_a_4857_ = leanh::lean_ctor_get(v___x_4846_, 0);
                                        leanh::lean_inc(v_a_4857_);
                                        leanh::lean_dec_ref_known(v___x_4846_, 1);
                                        if leanh::lean_obj_tag(v_a_4857_) == 0 {
                                            leanh::lean_dec_ref_known(v_a_4857_, 2);
                                            v___x_4858_ = 0;
                                            v___x_4859_ =
                                                lean_io_prim_handle_mk(v___x_4599_, v___x_4858_);
                                            if leanh::lean_obj_tag(v___x_4859_) == 0 {
                                                v_a_4860_ =
                                                    leanh::lean_ctor_get(v___x_4859_, 0);
                                                leanh::lean_inc(v_a_4860_);
                                                leanh::lean_dec_ref_known(v___x_4859_, 1);
                                                v_h_4758_ = v_a_4860_;
                                                v___y_4759_ = v_a_4556_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_dec_ref(v___x_4742_);
                                                leanh::lean_dec_ref(v___x_4599_);
                                                leanh::lean_dec_ref(v___x_4596_);
                                                leanh::lean_dec(v_a_4593_);
                                                leanh::lean_dec_ref(v_leanOpts_4577_);
                                                leanh::lean_dec(v_lakeOpts_4576_);
                                                leanh::lean_dec_ref(v_configFile_4575_);
                                                leanh::lean_dec_ref(v_pkgDir_4574_);
                                                leanh::lean_dec(v_pkgName_4573_);
                                                leanh::lean_dec(v_pkgIdx_4572_);
                                                leanh::lean_dec_ref(v_lakeEnv_4570_);
                                                v_a_4861_ =
                                                    leanh::lean_ctor_get(v___x_4859_, 0);
                                                leanh::lean_inc(v_a_4861_);
                                                leanh::lean_dec_ref_known(v___x_4859_, 1);
                                                v___x_4862_ = lean_io_error_to_string(v_a_4861_);
                                                v___x_4863_ = 3;
                                                v___x_4864_ =
                                                    leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_4864_,
                                                    0,
                                                    v___x_4862_,
                                                );
                                                leanh::lean_ctor_set_uint8(
                                                    v___x_4864_,
                                                    (core::mem::size_of::<
                                                        *mut leanh::LeanObject,
                                                    >(
                                                    ) * 1)
                                                        as u32,
                                                    v___x_4863_,
                                                );
                                                v___x_4865_ = lean_array_get_size(v_a_4556_);
                                                v___x_4866_ =
                                                    lean_array_push(v_a_4556_, v___x_4864_);
                                                v___x_4867_ =
                                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_4867_,
                                                    0,
                                                    v___x_4865_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_4867_,
                                                    1,
                                                    v___x_4866_,
                                                );
                                                return v___x_4867_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_4742_);
                                            leanh::lean_dec_ref(v___x_4599_);
                                            leanh::lean_dec_ref(v___x_4596_);
                                            leanh::lean_dec(v_a_4593_);
                                            leanh::lean_dec_ref(v_leanOpts_4577_);
                                            leanh::lean_dec(v_lakeOpts_4576_);
                                            leanh::lean_dec_ref(v_configFile_4575_);
                                            leanh::lean_dec_ref(v_pkgDir_4574_);
                                            leanh::lean_dec(v_pkgName_4573_);
                                            leanh::lean_dec(v_pkgIdx_4572_);
                                            leanh::lean_dec_ref(v_lakeEnv_4570_);
                                            v___x_4868_ = lean_io_error_to_string(v_a_4857_);
                                            v___x_4869_ = 3;
                                            v___x_4870_ =
                                                leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_4870_,
                                                0,
                                                v___x_4868_,
                                            );
                                            leanh::lean_ctor_set_uint8(
                                                v___x_4870_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 1)
                                                    as u32,
                                                v___x_4869_,
                                            );
                                            v___x_4871_ = lean_array_get_size(v_a_4556_);
                                            v___x_4872_ = lean_array_push(v_a_4556_, v___x_4870_);
                                            v___x_4873_ =
                                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_4873_,
                                                0,
                                                v___x_4871_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_4873_,
                                                1,
                                                v___x_4872_,
                                            );
                                            return v___x_4873_;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_4742_);
                                    leanh::lean_dec_ref(v___x_4599_);
                                    leanh::lean_dec_ref(v___x_4596_);
                                    leanh::lean_dec(v_a_4593_);
                                    leanh::lean_dec_ref(v_leanOpts_4577_);
                                    leanh::lean_dec(v_lakeOpts_4576_);
                                    leanh::lean_dec_ref(v_configFile_4575_);
                                    leanh::lean_dec_ref(v_pkgDir_4574_);
                                    leanh::lean_dec(v_pkgName_4573_);
                                    leanh::lean_dec(v_pkgIdx_4572_);
                                    leanh::lean_dec_ref(v_lakeEnv_4570_);
                                    v_a_4874_ = leanh::lean_ctor_get(v___x_4844_, 0);
                                    leanh::lean_inc(v_a_4874_);
                                    leanh::lean_dec_ref_known(v___x_4844_, 1);
                                    v___x_4875_ = lean_io_error_to_string(v_a_4874_);
                                    v___x_4876_ = 3;
                                    v___x_4877_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                    leanh::lean_ctor_set(v___x_4877_, 0, v___x_4875_);
                                    leanh::lean_ctor_set_uint8(
                                        v___x_4877_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_4876_,
                                    );
                                    v___x_4878_ = lean_array_get_size(v_a_4556_);
                                    v___x_4879_ = lean_array_push(v_a_4556_, v___x_4877_);
                                    v___x_4880_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_4878_);
                                    leanh::lean_ctor_set(v___x_4880_, 1, v___x_4879_);
                                    return v___x_4880_;
                                }
                            } else {
                                v___x_4881_ = 0;
                                v___x_4882_ = lean_io_prim_handle_mk(v___x_4599_, v___x_4881_);
                                if leanh::lean_obj_tag(v___x_4882_) == 0 {
                                    v_a_4883_ = leanh::lean_ctor_get(v___x_4882_, 0);
                                    leanh::lean_inc(v_a_4883_);
                                    leanh::lean_dec_ref_known(v___x_4882_, 1);
                                    v_h_4758_ = v_a_4883_;
                                    v___y_4759_ = v_a_4556_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___x_4742_);
                                    leanh::lean_dec_ref(v___x_4599_);
                                    leanh::lean_dec_ref(v___x_4596_);
                                    leanh::lean_dec(v_a_4593_);
                                    leanh::lean_dec_ref(v_leanOpts_4577_);
                                    leanh::lean_dec(v_lakeOpts_4576_);
                                    leanh::lean_dec_ref(v_configFile_4575_);
                                    leanh::lean_dec_ref(v_pkgDir_4574_);
                                    leanh::lean_dec(v_pkgName_4573_);
                                    leanh::lean_dec(v_pkgIdx_4572_);
                                    leanh::lean_dec_ref(v_lakeEnv_4570_);
                                    v_a_4884_ = leanh::lean_ctor_get(v___x_4882_, 0);
                                    leanh::lean_inc(v_a_4884_);
                                    leanh::lean_dec_ref_known(v___x_4882_, 1);
                                    v___x_4885_ = lean_io_error_to_string(v_a_4884_);
                                    v___x_4886_ = 3;
                                    v___x_4887_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                    leanh::lean_ctor_set(v___x_4887_, 0, v___x_4885_);
                                    leanh::lean_ctor_set_uint8(
                                        v___x_4887_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_4886_,
                                    );
                                    v___x_4888_ = lean_array_get_size(v_a_4556_);
                                    v___x_4889_ = lean_array_push(v_a_4556_, v___x_4887_);
                                    v___x_4890_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4890_, 0, v___x_4888_);
                                    leanh::lean_ctor_set(v___x_4890_, 1, v___x_4889_);
                                    return v___x_4890_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_configDir_4590_);
                            leanh::lean_dec(v_val_4584_);
                            leanh::lean_dec_ref(v_leanOpts_4577_);
                            leanh::lean_dec(v_lakeOpts_4576_);
                            leanh::lean_dec_ref(v_configFile_4575_);
                            leanh::lean_dec_ref(v_pkgDir_4574_);
                            leanh::lean_dec(v_pkgName_4573_);
                            leanh::lean_dec(v_pkgIdx_4572_);
                            leanh::lean_dec_ref(v_lakeEnv_4570_);
                            v_a_4891_ = leanh::lean_ctor_get(v___x_4592_, 0);
                            leanh::lean_inc(v_a_4891_);
                            leanh::lean_dec_ref_known(v___x_4592_, 1);
                            v___x_4892_ = lean_io_error_to_string(v_a_4891_);
                            v___x_4893_ = 3;
                            v___x_4894_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_4894_, 0, v___x_4892_);
                            leanh::lean_ctor_set_uint8(
                                v___x_4894_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_4893_,
                            );
                            v___x_4895_ = lean_array_get_size(v_a_4556_);
                            v___x_4896_ = lean_array_push(v_a_4556_, v___x_4894_);
                            v___x_4897_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4897_, 0, v___x_4895_);
                            leanh::lean_ctor_set(v___x_4897_, 1, v___x_4896_);
                            return v___x_4897_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_configDir_4590_);
                        leanh::lean_dec(v_val_4584_);
                        leanh::lean_dec_ref(v_leanOpts_4577_);
                        leanh::lean_dec(v_lakeOpts_4576_);
                        leanh::lean_dec_ref(v_configFile_4575_);
                        leanh::lean_dec_ref(v_pkgDir_4574_);
                        leanh::lean_dec(v_pkgName_4573_);
                        leanh::lean_dec(v_pkgIdx_4572_);
                        leanh::lean_dec_ref(v_lakeEnv_4570_);
                        v_a_4898_ = leanh::lean_ctor_get(v___x_4591_, 0);
                        leanh::lean_inc(v_a_4898_);
                        leanh::lean_dec_ref_known(v___x_4591_, 1);
                        v___x_4899_ = lean_io_error_to_string(v_a_4898_);
                        v___x_4900_ = 3;
                        v___x_4901_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_4901_, 0, v___x_4899_);
                        leanh::lean_ctor_set_uint8(
                            v___x_4901_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_4900_,
                        );
                        v___x_4902_ = lean_array_get_size(v_a_4556_);
                        v___x_4903_ = lean_array_push(v_a_4556_, v___x_4901_);
                        v___x_4904_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4904_, 0, v___x_4902_);
                        leanh::lean_ctor_set(v___x_4904_, 1, v___x_4903_);
                        return v___x_4904_;
                    }
                }
            }
            1 => {
                v___x_4561_ = 3;
                leanh::lean_inc_ref(v___y_4560_);
                v___x_4562_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4562_, 0, v___y_4560_);
                leanh::lean_ctor_set_uint8(
                    v___x_4562_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4561_,
                );
                v___x_4563_ = lean_array_get_size(v___y_4559_);
                v___x_4564_ = lean_array_push(v___y_4559_, v___x_4562_);
                v___x_4565_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4565_, 0, v___x_4563_);
                leanh::lean_ctor_set(v___x_4565_, 1, v___x_4564_);
                return v___x_4565_;
            }
            2 => {
                v___x_4569_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4569_, 0, v___y_4567_);
                leanh::lean_ctor_set(v___x_4569_, 1, v_a_4568_);
                return v___x_4569_;
            }
            3 => {
                v___x_4604_ = lean_io_remove_file(v___x_4596_);
                if leanh::lean_obj_tag(v___x_4604_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4604_, 1);
                    leanh::lean_dec_ref(v___x_4599_);
                    v___x_4605_ = l_System_Platform_target;
                    v___x_4606_ = l_Lake_Env_leanGithash(v_lakeEnv_4570_);
                    leanh::lean_dec_ref(v_lakeEnv_4570_);
                    leanh::lean_inc(v_lakeOpts_4602_);
                    leanh::lean_inc(v_pkgName_4573_);
                    leanh::lean_inc(v_pkgIdx_4572_);
                    v___x_4607_ = leanh::lean_alloc_ctor(0, 5, (8) as u32);
                    leanh::lean_ctor_set(v___x_4607_, 0, v_pkgIdx_4572_);
                    leanh::lean_ctor_set(v___x_4607_, 1, v_pkgName_4573_);
                    leanh::lean_ctor_set(v___x_4607_, 2, v___x_4605_);
                    leanh::lean_ctor_set(v___x_4607_, 3, v___x_4606_);
                    leanh::lean_ctor_set(v___x_4607_, 4, v_lakeOpts_4602_);
                    v___x_4608_ = leanh::lean_unbox_uint64(v_a_4593_);
                    leanh::lean_dec(v_a_4593_);
                    leanh::lean_ctor_set_uint64(
                        v___x_4607_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v___x_4608_,
                    );
                    v___x_4609_ =
                        l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(
                            v___x_4607_,
                        );
                    v___x_4610_ = leanh::lean_unsigned_to_nat(80);
                    v___x_4611_ = l_Lean_Json_pretty(v___x_4609_, v___x_4610_);
                    v___x_4612_ = l_IO_FS_Handle_putStrLn(v_h_4601_, v___x_4611_);
                    if leanh::lean_obj_tag(v___x_4612_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4612_, 1);
                        v___x_4613_ = lean_io_prim_handle_truncate(v_h_4601_);
                        if leanh::lean_obj_tag(v___x_4613_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4613_, 1);
                            v___x_4614_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(
                                v_pkgIdx_4572_,
                                v_pkgName_4573_,
                                v_pkgDir_4574_,
                                v_lakeOpts_4602_,
                                v_leanOpts_4577_,
                                v_configFile_4575_,
                                v___y_4603_,
                            );
                            if leanh::lean_obj_tag(v___x_4614_) == 0 {
                                v_a_4615_ = leanh::lean_ctor_get(v___x_4614_, 0);
                                leanh::lean_inc(v_a_4615_);
                                v_a_4616_ = leanh::lean_ctor_get(v___x_4614_, 1);
                                leanh::lean_inc(v_a_4616_);
                                v___x_4617_ = 1;
                                v___x_4618_ =
                                    l_Lean_writeModule(v_a_4615_, v___x_4596_, v___x_4617_);
                                if leanh::lean_obj_tag(v___x_4618_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4618_, 1);
                                    v___x_4619_ = lean_io_prim_handle_unlock(v_h_4601_);
                                    leanh::lean_dec(v_h_4601_);
                                    if leanh::lean_obj_tag(v___x_4619_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4619_, 1);
                                        leanh::lean_dec(v_a_4616_);
                                        return v___x_4614_;
                                    } else {
                                        v_isSharedCheck_4632_ =
                                            (!leanh::lean_is_exclusive(v___x_4614_)) as u8;
                                        if v_isSharedCheck_4632_ == 0 {
                                            v_unused_4633_ =
                                                leanh::lean_ctor_get(v___x_4614_, 1);
                                            leanh::lean_dec(v_unused_4633_);
                                            v_unused_4634_ =
                                                leanh::lean_ctor_get(v___x_4614_, 0);
                                            leanh::lean_dec(v_unused_4634_);
                                            v___x_4621_ = v___x_4614_;
                                            v_isShared_4622_ = v_isSharedCheck_4632_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_4614_);
                                            v___x_4621_ = leanh::lean_box(0);
                                            v_isShared_4622_ = v_isSharedCheck_4632_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_h_4601_);
                                    v_isSharedCheck_4647_ =
                                        (!leanh::lean_is_exclusive(v___x_4614_)) as u8;
                                    if v_isSharedCheck_4647_ == 0 {
                                        v_unused_4648_ =
                                            leanh::lean_ctor_get(v___x_4614_, 1);
                                        leanh::lean_dec(v_unused_4648_);
                                        v_unused_4649_ =
                                            leanh::lean_ctor_get(v___x_4614_, 0);
                                        leanh::lean_dec(v_unused_4649_);
                                        v___x_4636_ = v___x_4614_;
                                        v_isShared_4637_ = v_isSharedCheck_4647_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_4614_);
                                        v___x_4636_ = leanh::lean_box(0);
                                        v_isShared_4637_ = v_isSharedCheck_4647_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_h_4601_);
                                leanh::lean_dec_ref(v___x_4596_);
                                return v___x_4614_;
                            }
                        } else {
                            leanh::lean_dec(v_lakeOpts_4602_);
                            leanh::lean_dec(v_h_4601_);
                            leanh::lean_dec_ref(v___x_4596_);
                            leanh::lean_dec_ref(v_leanOpts_4577_);
                            leanh::lean_dec_ref(v_configFile_4575_);
                            leanh::lean_dec_ref(v_pkgDir_4574_);
                            leanh::lean_dec(v_pkgName_4573_);
                            leanh::lean_dec(v_pkgIdx_4572_);
                            v_a_4650_ = leanh::lean_ctor_get(v___x_4613_, 0);
                            leanh::lean_inc(v_a_4650_);
                            leanh::lean_dec_ref_known(v___x_4613_, 1);
                            v___x_4651_ = lean_io_error_to_string(v_a_4650_);
                            v___x_4652_ = 3;
                            v___x_4653_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_4653_, 0, v___x_4651_);
                            leanh::lean_ctor_set_uint8(
                                v___x_4653_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_4652_,
                            );
                            v___x_4654_ = lean_array_get_size(v___y_4603_);
                            v___x_4655_ = lean_array_push(v___y_4603_, v___x_4653_);
                            v___x_4656_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4656_, 0, v___x_4654_);
                            leanh::lean_ctor_set(v___x_4656_, 1, v___x_4655_);
                            return v___x_4656_;
                        }
                    } else {
                        leanh::lean_dec(v_lakeOpts_4602_);
                        leanh::lean_dec(v_h_4601_);
                        leanh::lean_dec_ref(v___x_4596_);
                        leanh::lean_dec_ref(v_leanOpts_4577_);
                        leanh::lean_dec_ref(v_configFile_4575_);
                        leanh::lean_dec_ref(v_pkgDir_4574_);
                        leanh::lean_dec(v_pkgName_4573_);
                        leanh::lean_dec(v_pkgIdx_4572_);
                        v_a_4657_ = leanh::lean_ctor_get(v___x_4612_, 0);
                        leanh::lean_inc(v_a_4657_);
                        leanh::lean_dec_ref_known(v___x_4612_, 1);
                        v___x_4658_ = lean_io_error_to_string(v_a_4657_);
                        v___x_4659_ = 3;
                        v___x_4660_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_4660_, 0, v___x_4658_);
                        leanh::lean_ctor_set_uint8(
                            v___x_4660_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_4659_,
                        );
                        v___x_4661_ = lean_array_get_size(v___y_4603_);
                        v___x_4662_ = lean_array_push(v___y_4603_, v___x_4660_);
                        v___x_4663_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4663_, 0, v___x_4661_);
                        leanh::lean_ctor_set(v___x_4663_, 1, v___x_4662_);
                        return v___x_4663_;
                    }
                } else {
                    v_a_4664_ = leanh::lean_ctor_get(v___x_4604_, 0);
                    leanh::lean_inc(v_a_4664_);
                    leanh::lean_dec_ref_known(v___x_4604_, 1);
                    if leanh::lean_obj_tag(v_a_4664_) == 11 {
                        leanh::lean_dec_ref_known(v_a_4664_, 2);
                        leanh::lean_dec_ref(v___x_4599_);
                        v___x_4665_ = l_System_Platform_target;
                        v___x_4666_ = l_Lake_Env_leanGithash(v_lakeEnv_4570_);
                        leanh::lean_dec_ref(v_lakeEnv_4570_);
                        leanh::lean_inc(v_lakeOpts_4602_);
                        leanh::lean_inc(v_pkgName_4573_);
                        leanh::lean_inc(v_pkgIdx_4572_);
                        v___x_4667_ = leanh::lean_alloc_ctor(0, 5, (8) as u32);
                        leanh::lean_ctor_set(v___x_4667_, 0, v_pkgIdx_4572_);
                        leanh::lean_ctor_set(v___x_4667_, 1, v_pkgName_4573_);
                        leanh::lean_ctor_set(v___x_4667_, 2, v___x_4665_);
                        leanh::lean_ctor_set(v___x_4667_, 3, v___x_4666_);
                        leanh::lean_ctor_set(v___x_4667_, 4, v_lakeOpts_4602_);
                        v___x_4668_ = leanh::lean_unbox_uint64(v_a_4593_);
                        leanh::lean_dec(v_a_4593_);
                        leanh::lean_ctor_set_uint64(
                            v___x_4667_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                            v___x_4668_,
                        );
                        v___x_4669_ =
                            l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(
                                v___x_4667_,
                            );
                        v___x_4670_ = leanh::lean_unsigned_to_nat(80);
                        v___x_4671_ = l_Lean_Json_pretty(v___x_4669_, v___x_4670_);
                        v___x_4672_ = l_IO_FS_Handle_putStrLn(v_h_4601_, v___x_4671_);
                        if leanh::lean_obj_tag(v___x_4672_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4672_, 1);
                            v___x_4673_ = lean_io_prim_handle_truncate(v_h_4601_);
                            if leanh::lean_obj_tag(v___x_4673_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4673_, 1);
                                v___x_4674_ =
                                    l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(
                                        v_pkgIdx_4572_,
                                        v_pkgName_4573_,
                                        v_pkgDir_4574_,
                                        v_lakeOpts_4602_,
                                        v_leanOpts_4577_,
                                        v_configFile_4575_,
                                        v___y_4603_,
                                    );
                                if leanh::lean_obj_tag(v___x_4674_) == 0 {
                                    v_a_4675_ = leanh::lean_ctor_get(v___x_4674_, 0);
                                    leanh::lean_inc(v_a_4675_);
                                    v_a_4676_ = leanh::lean_ctor_get(v___x_4674_, 1);
                                    leanh::lean_inc(v_a_4676_);
                                    v___x_4677_ = 1;
                                    v___x_4678_ =
                                        l_Lean_writeModule(v_a_4675_, v___x_4596_, v___x_4677_);
                                    if leanh::lean_obj_tag(v___x_4678_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4678_, 1);
                                        v___x_4679_ = lean_io_prim_handle_unlock(v_h_4601_);
                                        leanh::lean_dec(v_h_4601_);
                                        if leanh::lean_obj_tag(v___x_4679_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_4679_, 1);
                                            leanh::lean_dec(v_a_4676_);
                                            return v___x_4674_;
                                        } else {
                                            v_isSharedCheck_4692_ =
                                                (!leanh::lean_is_exclusive(v___x_4674_))
                                                    as u8;
                                            if v_isSharedCheck_4692_ == 0 {
                                                v_unused_4693_ =
                                                    leanh::lean_ctor_get(v___x_4674_, 1);
                                                leanh::lean_dec(v_unused_4693_);
                                                v_unused_4694_ =
                                                    leanh::lean_ctor_get(v___x_4674_, 0);
                                                leanh::lean_dec(v_unused_4694_);
                                                v___x_4681_ = v___x_4674_;
                                                v_isShared_4682_ = v_isSharedCheck_4692_;
                                                state = 8;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___x_4674_);
                                                v___x_4681_ = leanh::lean_box(0);
                                                v_isShared_4682_ = v_isSharedCheck_4692_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_h_4601_);
                                        v_isSharedCheck_4707_ =
                                            (!leanh::lean_is_exclusive(v___x_4674_)) as u8;
                                        if v_isSharedCheck_4707_ == 0 {
                                            v_unused_4708_ =
                                                leanh::lean_ctor_get(v___x_4674_, 1);
                                            leanh::lean_dec(v_unused_4708_);
                                            v_unused_4709_ =
                                                leanh::lean_ctor_get(v___x_4674_, 0);
                                            leanh::lean_dec(v_unused_4709_);
                                            v___x_4696_ = v___x_4674_;
                                            v_isShared_4697_ = v_isSharedCheck_4707_;
                                            state = 10;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_4674_);
                                            v___x_4696_ = leanh::lean_box(0);
                                            v_isShared_4697_ = v_isSharedCheck_4707_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_h_4601_);
                                    leanh::lean_dec_ref(v___x_4596_);
                                    return v___x_4674_;
                                }
                            } else {
                                leanh::lean_dec(v_lakeOpts_4602_);
                                leanh::lean_dec(v_h_4601_);
                                leanh::lean_dec_ref(v___x_4596_);
                                leanh::lean_dec_ref(v_leanOpts_4577_);
                                leanh::lean_dec_ref(v_configFile_4575_);
                                leanh::lean_dec_ref(v_pkgDir_4574_);
                                leanh::lean_dec(v_pkgName_4573_);
                                leanh::lean_dec(v_pkgIdx_4572_);
                                v_a_4710_ = leanh::lean_ctor_get(v___x_4673_, 0);
                                leanh::lean_inc(v_a_4710_);
                                leanh::lean_dec_ref_known(v___x_4673_, 1);
                                v___x_4711_ = lean_io_error_to_string(v_a_4710_);
                                v___x_4712_ = 3;
                                v___x_4713_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                leanh::lean_ctor_set(v___x_4713_, 0, v___x_4711_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_4713_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_4712_,
                                );
                                v___x_4714_ = lean_array_get_size(v___y_4603_);
                                v___x_4715_ = lean_array_push(v___y_4603_, v___x_4713_);
                                v___x_4716_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4716_, 0, v___x_4714_);
                                leanh::lean_ctor_set(v___x_4716_, 1, v___x_4715_);
                                return v___x_4716_;
                            }
                        } else {
                            leanh::lean_dec(v_lakeOpts_4602_);
                            leanh::lean_dec(v_h_4601_);
                            leanh::lean_dec_ref(v___x_4596_);
                            leanh::lean_dec_ref(v_leanOpts_4577_);
                            leanh::lean_dec_ref(v_configFile_4575_);
                            leanh::lean_dec_ref(v_pkgDir_4574_);
                            leanh::lean_dec(v_pkgName_4573_);
                            leanh::lean_dec(v_pkgIdx_4572_);
                            v_a_4717_ = leanh::lean_ctor_get(v___x_4672_, 0);
                            leanh::lean_inc(v_a_4717_);
                            leanh::lean_dec_ref_known(v___x_4672_, 1);
                            v___x_4718_ = lean_io_error_to_string(v_a_4717_);
                            v___x_4719_ = 3;
                            v___x_4720_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_4720_, 0, v___x_4718_);
                            leanh::lean_ctor_set_uint8(
                                v___x_4720_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_4719_,
                            );
                            v___x_4721_ = lean_array_get_size(v___y_4603_);
                            v___x_4722_ = lean_array_push(v___y_4603_, v___x_4720_);
                            v___x_4723_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4723_, 0, v___x_4721_);
                            leanh::lean_ctor_set(v___x_4723_, 1, v___x_4722_);
                            return v___x_4723_;
                        }
                    } else {
                        leanh::lean_dec(v_lakeOpts_4602_);
                        leanh::lean_dec_ref(v___x_4596_);
                        leanh::lean_dec(v_a_4593_);
                        leanh::lean_dec_ref(v_leanOpts_4577_);
                        leanh::lean_dec_ref(v_configFile_4575_);
                        leanh::lean_dec_ref(v_pkgDir_4574_);
                        leanh::lean_dec(v_pkgName_4573_);
                        leanh::lean_dec(v_pkgIdx_4572_);
                        leanh::lean_dec_ref(v_lakeEnv_4570_);
                        v___x_4724_ = lean_io_error_to_string(v_a_4664_);
                        v___x_4725_ = 3;
                        v___x_4726_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_4726_, 0, v___x_4724_);
                        leanh::lean_ctor_set_uint8(
                            v___x_4726_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_4725_,
                        );
                        v___x_4727_ = lean_array_get_size(v___y_4603_);
                        v___x_4728_ = lean_array_push(v___y_4603_, v___x_4726_);
                        v___x_4729_ = lean_io_prim_handle_unlock(v_h_4601_);
                        leanh::lean_dec(v_h_4601_);
                        if leanh::lean_obj_tag(v___x_4729_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4729_, 1);
                            v___x_4730_ = lean_io_remove_file(v___x_4599_);
                            leanh::lean_dec_ref(v___x_4599_);
                            if leanh::lean_obj_tag(v___x_4730_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4730_, 1);
                                v___y_4567_ = v___x_4727_;
                                v_a_4568_ = v___x_4728_;
                                state = 2;
                                continue;
                            } else {
                                v_a_4731_ = leanh::lean_ctor_get(v___x_4730_, 0);
                                leanh::lean_inc(v_a_4731_);
                                leanh::lean_dec_ref_known(v___x_4730_, 1);
                                v___x_4732_ = lean_io_error_to_string(v_a_4731_);
                                v___x_4733_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                leanh::lean_ctor_set(v___x_4733_, 0, v___x_4732_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_4733_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_4725_,
                                );
                                v___x_4734_ = lean_array_push(v___x_4728_, v___x_4733_);
                                v___y_4567_ = v___x_4727_;
                                v_a_4568_ = v___x_4734_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_4599_);
                            v_a_4735_ = leanh::lean_ctor_get(v___x_4729_, 0);
                            leanh::lean_inc(v_a_4735_);
                            leanh::lean_dec_ref_known(v___x_4729_, 1);
                            v___x_4736_ = lean_io_error_to_string(v_a_4735_);
                            v___x_4737_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_4737_, 0, v___x_4736_);
                            leanh::lean_ctor_set_uint8(
                                v___x_4737_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_4725_,
                            );
                            v___x_4738_ = lean_array_push(v___x_4728_, v___x_4737_);
                            v___y_4567_ = v___x_4727_;
                            v_a_4568_ = v___x_4738_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_a_4623_ = leanh::lean_ctor_get(v___x_4619_, 0);
                leanh::lean_inc(v_a_4623_);
                leanh::lean_dec_ref_known(v___x_4619_, 1);
                v___x_4624_ = lean_io_error_to_string(v_a_4623_);
                v___x_4625_ = 3;
                v___x_4626_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4626_, 0, v___x_4624_);
                leanh::lean_ctor_set_uint8(
                    v___x_4626_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4625_,
                );
                v___x_4627_ = lean_array_get_size(v_a_4616_);
                v___x_4628_ = lean_array_push(v_a_4616_, v___x_4626_);
                if v_isShared_4622_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4621_, 1);
                    leanh::lean_ctor_set(v___x_4621_, 1, v___x_4628_);
                    leanh::lean_ctor_set(v___x_4621_, 0, v___x_4627_);
                    v___x_4630_ = v___x_4621_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 1, v___x_4628_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4630_;
            }
            6 => {
                v_a_4638_ = leanh::lean_ctor_get(v___x_4618_, 0);
                leanh::lean_inc(v_a_4638_);
                leanh::lean_dec_ref_known(v___x_4618_, 1);
                v___x_4639_ = lean_io_error_to_string(v_a_4638_);
                v___x_4640_ = 3;
                v___x_4641_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4641_, 0, v___x_4639_);
                leanh::lean_ctor_set_uint8(
                    v___x_4641_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4640_,
                );
                v___x_4642_ = lean_array_get_size(v_a_4616_);
                v___x_4643_ = lean_array_push(v_a_4616_, v___x_4641_);
                if v_isShared_4637_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4636_, 1);
                    leanh::lean_ctor_set(v___x_4636_, 1, v___x_4643_);
                    leanh::lean_ctor_set(v___x_4636_, 0, v___x_4642_);
                    v___x_4645_ = v___x_4636_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4646_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4646_, 1, v___x_4643_);
                    v___x_4645_ = v_reuseFailAlloc_4646_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4645_;
            }
            8 => {
                v_a_4683_ = leanh::lean_ctor_get(v___x_4679_, 0);
                leanh::lean_inc(v_a_4683_);
                leanh::lean_dec_ref_known(v___x_4679_, 1);
                v___x_4684_ = lean_io_error_to_string(v_a_4683_);
                v___x_4685_ = 3;
                v___x_4686_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4686_, 0, v___x_4684_);
                leanh::lean_ctor_set_uint8(
                    v___x_4686_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4685_,
                );
                v___x_4687_ = lean_array_get_size(v_a_4676_);
                v___x_4688_ = lean_array_push(v_a_4676_, v___x_4686_);
                if v_isShared_4682_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4681_, 1);
                    leanh::lean_ctor_set(v___x_4681_, 1, v___x_4688_);
                    leanh::lean_ctor_set(v___x_4681_, 0, v___x_4687_);
                    v___x_4690_ = v___x_4681_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4691_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 1, v___x_4688_);
                    v___x_4690_ = v_reuseFailAlloc_4691_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4690_;
            }
            10 => {
                v_a_4698_ = leanh::lean_ctor_get(v___x_4678_, 0);
                leanh::lean_inc(v_a_4698_);
                leanh::lean_dec_ref_known(v___x_4678_, 1);
                v___x_4699_ = lean_io_error_to_string(v_a_4698_);
                v___x_4700_ = 3;
                v___x_4701_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4701_, 0, v___x_4699_);
                leanh::lean_ctor_set_uint8(
                    v___x_4701_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4700_,
                );
                v___x_4702_ = lean_array_get_size(v_a_4676_);
                v___x_4703_ = lean_array_push(v_a_4676_, v___x_4701_);
                if v_isShared_4697_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4696_, 1);
                    leanh::lean_ctor_set(v___x_4696_, 1, v___x_4703_);
                    leanh::lean_ctor_set(v___x_4696_, 0, v___x_4702_);
                    v___x_4705_ = v___x_4696_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4706_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4706_, 1, v___x_4703_);
                    v___x_4705_ = v_reuseFailAlloc_4706_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4705_;
            }
            12 => {
                v___x_4747_ =
                    l_Lake_importConfigFile___lam__0(v___x_4742_, v___x_4599_, v___y_4746_);
                leanh::lean_dec(v___y_4746_);
                leanh::lean_dec_ref(v___x_4742_);
                if leanh::lean_obj_tag(v___x_4747_) == 0 {
                    v_a_4748_ = leanh::lean_ctor_get(v___x_4747_, 0);
                    leanh::lean_inc(v_a_4748_);
                    leanh::lean_dec_ref_known(v___x_4747_, 1);
                    v_options_4749_ = leanh::lean_ctor_get(v___y_4745_, 4);
                    leanh::lean_inc(v_options_4749_);
                    leanh::lean_dec_ref(v___y_4745_);
                    v_h_4601_ = v_a_4748_;
                    v_lakeOpts_4602_ = v_options_4749_;
                    v___y_4603_ = v___y_4744_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4745_);
                    leanh::lean_dec_ref(v___x_4599_);
                    leanh::lean_dec_ref(v___x_4596_);
                    leanh::lean_dec(v_a_4593_);
                    leanh::lean_dec_ref(v_leanOpts_4577_);
                    leanh::lean_dec_ref(v_configFile_4575_);
                    leanh::lean_dec_ref(v_pkgDir_4574_);
                    leanh::lean_dec(v_pkgName_4573_);
                    leanh::lean_dec(v_pkgIdx_4572_);
                    leanh::lean_dec_ref(v_lakeEnv_4570_);
                    v_a_4750_ = leanh::lean_ctor_get(v___x_4747_, 0);
                    leanh::lean_inc(v_a_4750_);
                    leanh::lean_dec_ref_known(v___x_4747_, 1);
                    v___x_4751_ = lean_io_error_to_string(v_a_4750_);
                    v___x_4752_ = 3;
                    v___x_4753_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_4753_, 0, v___x_4751_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4753_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_4752_,
                    );
                    v___x_4754_ = lean_array_get_size(v___y_4744_);
                    v___x_4755_ = lean_array_push(v___y_4744_, v___x_4753_);
                    v___x_4756_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4756_, 0, v___x_4754_);
                    leanh::lean_ctor_set(v___x_4756_, 1, v___x_4755_);
                    return v___x_4756_;
                }
            }
            13 => {
                if v_reconfigure_4578_ == 0 {
                    leanh::lean_dec(v_lakeOpts_4576_);
                    v___x_4760_ = lean_io_prim_handle_lock(v_h_4758_, v_reconfigure_4578_);
                    if leanh::lean_obj_tag(v___x_4760_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4760_, 1);
                        v___x_4761_ = l_IO_FS_Handle_readToEnd(v_h_4758_);
                        if leanh::lean_obj_tag(v___x_4761_) == 0 {
                            v_a_4762_ = leanh::lean_ctor_get(v___x_4761_, 0);
                            leanh::lean_inc(v_a_4762_);
                            leanh::lean_dec_ref_known(v___x_4761_, 1);
                            v___x_4763_ = l_Lake_importConfigFile___closed__6;
                            v___x_4764_ = l_Lean_Json_parse(v_a_4762_);
                            if leanh::lean_obj_tag(v___x_4764_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4764_, 1);
                                leanh::lean_dec(v_h_4758_);
                                leanh::lean_dec_ref(v___x_4742_);
                                leanh::lean_dec_ref(v___x_4599_);
                                leanh::lean_dec_ref(v___x_4596_);
                                leanh::lean_dec(v_a_4593_);
                                leanh::lean_dec_ref(v_leanOpts_4577_);
                                leanh::lean_dec_ref(v_configFile_4575_);
                                leanh::lean_dec_ref(v_pkgDir_4574_);
                                leanh::lean_dec(v_pkgName_4573_);
                                leanh::lean_dec(v_pkgIdx_4572_);
                                leanh::lean_dec_ref(v_lakeEnv_4570_);
                                v___x_4765_ = l_Lake_importConfigFile___closed__7;
                                v___x_4766_ = lean_array_get_size(v___y_4759_);
                                v___x_4767_ = lean_array_push(v___y_4759_, v___x_4765_);
                                v___x_4768_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4768_, 0, v___x_4766_);
                                leanh::lean_ctor_set(v___x_4768_, 1, v___x_4767_);
                                return v___x_4768_;
                            } else {
                                v_a_4769_ = leanh::lean_ctor_get(v___x_4764_, 0);
                                leanh::lean_inc_n(v_a_4769_, 2);
                                leanh::lean_dec_ref_known(v___x_4764_, 1);
                                v___x_4770_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_4769_);
                                if leanh::lean_obj_tag(v___x_4770_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4770_, 1);
                                    v___x_4771_ = l_Lean_Json_getObj_x3f(v_a_4769_);
                                    if leanh::lean_obj_tag(v___x_4771_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4771_, 1);
                                        leanh::lean_dec(v_h_4758_);
                                        leanh::lean_dec_ref(v___x_4742_);
                                        leanh::lean_dec_ref(v___x_4599_);
                                        leanh::lean_dec_ref(v___x_4596_);
                                        leanh::lean_dec(v_a_4593_);
                                        leanh::lean_dec_ref(v_leanOpts_4577_);
                                        leanh::lean_dec_ref(v_configFile_4575_);
                                        leanh::lean_dec_ref(v_pkgDir_4574_);
                                        leanh::lean_dec(v_pkgName_4573_);
                                        leanh::lean_dec(v_pkgIdx_4572_);
                                        leanh::lean_dec_ref(v_lakeEnv_4570_);
                                        v___y_4559_ = v___y_4759_;
                                        v___y_4560_ = v___x_4763_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_a_4772_ = leanh::lean_ctor_get(v___x_4771_, 0);
                                        leanh::lean_inc(v_a_4772_);
                                        leanh::lean_dec_ref_known(v___x_4771_, 1);
                                        v___x_4773_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5;
                                        v___x_4774_ =
                                            l_Lake_JsonObject_getJson_x3f(v_a_4772_, v___x_4773_);
                                        leanh::lean_dec(v_a_4772_);
                                        if leanh::lean_obj_tag(v___x_4774_) == 0 {
                                            leanh::lean_dec(v_h_4758_);
                                            leanh::lean_dec_ref(v___x_4742_);
                                            leanh::lean_dec_ref(v___x_4599_);
                                            leanh::lean_dec_ref(v___x_4596_);
                                            leanh::lean_dec(v_a_4593_);
                                            leanh::lean_dec_ref(v_leanOpts_4577_);
                                            leanh::lean_dec_ref(v_configFile_4575_);
                                            leanh::lean_dec_ref(v_pkgDir_4574_);
                                            leanh::lean_dec(v_pkgName_4573_);
                                            leanh::lean_dec(v_pkgIdx_4572_);
                                            leanh::lean_dec_ref(v_lakeEnv_4570_);
                                            v___y_4559_ = v___y_4759_;
                                            v___y_4560_ = v___x_4763_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_val_4775_ =
                                                leanh::lean_ctor_get(v___x_4774_, 0);
                                            leanh::lean_inc(v_val_4775_);
                                            leanh::lean_dec_ref_known(v___x_4774_, 1);
                                            v___x_4776_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_4775_);
                                            if leanh::lean_obj_tag(v___x_4776_) == 0 {
                                                leanh::lean_dec_ref_known(v___x_4776_, 1);
                                                leanh::lean_dec(v_h_4758_);
                                                leanh::lean_dec_ref(v___x_4742_);
                                                leanh::lean_dec_ref(v___x_4599_);
                                                leanh::lean_dec_ref(v___x_4596_);
                                                leanh::lean_dec(v_a_4593_);
                                                leanh::lean_dec_ref(v_leanOpts_4577_);
                                                leanh::lean_dec_ref(v_configFile_4575_);
                                                leanh::lean_dec_ref(v_pkgDir_4574_);
                                                leanh::lean_dec(v_pkgName_4573_);
                                                leanh::lean_dec(v_pkgIdx_4572_);
                                                leanh::lean_dec_ref(v_lakeEnv_4570_);
                                                v___y_4559_ = v___y_4759_;
                                                v___y_4560_ = v___x_4763_;
                                                state = 1;
                                                continue;
                                            } else {
                                                if leanh::lean_obj_tag(v___x_4776_) == 0 {
                                                    leanh::lean_dec_ref_known(
                                                        v___x_4776_,
                                                        1,
                                                    );
                                                    leanh::lean_dec(v_h_4758_);
                                                    leanh::lean_dec_ref(v___x_4742_);
                                                    leanh::lean_dec_ref(v___x_4599_);
                                                    leanh::lean_dec_ref(v___x_4596_);
                                                    leanh::lean_dec(v_a_4593_);
                                                    leanh::lean_dec_ref(v_leanOpts_4577_);
                                                    leanh::lean_dec_ref(v_configFile_4575_);
                                                    leanh::lean_dec_ref(v_pkgDir_4574_);
                                                    leanh::lean_dec(v_pkgName_4573_);
                                                    leanh::lean_dec(v_pkgIdx_4572_);
                                                    leanh::lean_dec_ref(v_lakeEnv_4570_);
                                                    v___y_4559_ = v___y_4759_;
                                                    v___y_4560_ = v___x_4763_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v_a_4777_ =
                                                        leanh::lean_ctor_get(v___x_4776_, 0);
                                                    leanh::lean_inc(v_a_4777_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_4776_,
                                                        1,
                                                    );
                                                    v___x_4778_ = l_Lake_importConfigFile___lam__0(
                                                        v___x_4742_,
                                                        v___x_4599_,
                                                        v_h_4758_,
                                                    );
                                                    leanh::lean_dec(v_h_4758_);
                                                    leanh::lean_dec_ref(v___x_4742_);
                                                    if leanh::lean_obj_tag(v___x_4778_) == 0
                                                    {
                                                        v_a_4779_ = leanh::lean_ctor_get(
                                                            v___x_4778_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_4779_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_4778_,
                                                            1,
                                                        );
                                                        v_h_4601_ = v_a_4779_;
                                                        v_lakeOpts_4602_ = v_a_4777_;
                                                        v___y_4603_ = v___y_4759_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        leanh::lean_dec(v_a_4777_);
                                                        leanh::lean_dec_ref(v___x_4599_);
                                                        leanh::lean_dec_ref(v___x_4596_);
                                                        leanh::lean_dec(v_a_4593_);
                                                        leanh::lean_dec_ref(
                                                            v_leanOpts_4577_,
                                                        );
                                                        leanh::lean_dec_ref(
                                                            v_configFile_4575_,
                                                        );
                                                        leanh::lean_dec_ref(v_pkgDir_4574_);
                                                        leanh::lean_dec(v_pkgName_4573_);
                                                        leanh::lean_dec(v_pkgIdx_4572_);
                                                        leanh::lean_dec_ref(v_lakeEnv_4570_);
                                                        v_a_4780_ = leanh::lean_ctor_get(
                                                            v___x_4778_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_4780_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_4778_,
                                                            1,
                                                        );
                                                        v___x_4781_ =
                                                            lean_io_error_to_string(v_a_4780_);
                                                        v___x_4782_ = 3;
                                                        v___x_4783_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (1) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_4783_,
                                                            0,
                                                            v___x_4781_,
                                                        );
                                                        leanh::lean_ctor_set_uint8(
                                                            v___x_4783_,
                                                            (core::mem::size_of::<
                                                                *mut leanh::LeanObject,
                                                            >(
                                                            ) * 1)
                                                                as u32,
                                                            v___x_4782_,
                                                        );
                                                        v___x_4784_ =
                                                            lean_array_get_size(v___y_4759_);
                                                        v___x_4785_ = lean_array_push(
                                                            v___y_4759_,
                                                            v___x_4783_,
                                                        );
                                                        v___x_4786_ = leanh::lean_alloc_ctor(
                                                            1,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_4786_,
                                                            0,
                                                            v___x_4784_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_4786_,
                                                            1,
                                                            v___x_4785_,
                                                        );
                                                        return v___x_4786_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4769_);
                                    v_a_4787_ = leanh::lean_ctor_get(v___x_4770_, 0);
                                    leanh::lean_inc(v_a_4787_);
                                    leanh::lean_dec_ref_known(v___x_4770_, 1);
                                    v___x_4788_ = l_System_FilePath_pathExists(v___x_4596_);
                                    if v___x_4788_ == 0 {
                                        v___y_4744_ = v___y_4759_;
                                        v___y_4745_ = v_a_4787_;
                                        v___y_4746_ = v_h_4758_;
                                        state = 12;
                                        continue;
                                    } else {
                                        v_idx_4789_ = leanh::lean_ctor_get(v_a_4787_, 0);
                                        v_name_4790_ = leanh::lean_ctor_get(v_a_4787_, 1);
                                        v_platform_4791_ =
                                            leanh::lean_ctor_get(v_a_4787_, 2);
                                        v_leanHash_4792_ =
                                            leanh::lean_ctor_get(v_a_4787_, 3);
                                        v_configHash_4793_ = leanh::lean_ctor_get_uint64(
                                            v_a_4787_,
                                            (core::mem::size_of::<*mut leanh::LeanObject>()
                                                * 5)
                                                as u32,
                                        );
                                        v___x_4794_ = lean_nat_dec_eq(v_idx_4789_, v_pkgIdx_4572_);
                                        if v___x_4794_ == 0 {
                                            v___y_4744_ = v___y_4759_;
                                            v___y_4745_ = v_a_4787_;
                                            v___y_4746_ = v_h_4758_;
                                            state = 12;
                                            continue;
                                        } else {
                                            v___x_4795_ =
                                                lean_name_eq(v_name_4790_, v_pkgName_4573_);
                                            if v___x_4795_ == 0 {
                                                v___y_4744_ = v___y_4759_;
                                                v___y_4745_ = v_a_4787_;
                                                v___y_4746_ = v_h_4758_;
                                                state = 12;
                                                continue;
                                            } else {
                                                v___x_4796_ =
                                                    leanh::lean_unbox_uint64(v_a_4593_);
                                                v___x_4797_ = lean_uint64_dec_eq(
                                                    v_configHash_4793_,
                                                    v___x_4796_,
                                                );
                                                if v___x_4797_ == 0 {
                                                    v___y_4744_ = v___y_4759_;
                                                    v___y_4745_ = v_a_4787_;
                                                    v___y_4746_ = v_h_4758_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    v___x_4798_ = l_System_Platform_target;
                                                    v___x_4799_ = lean_string_dec_eq(
                                                        v_platform_4791_,
                                                        v___x_4798_,
                                                    );
                                                    if v___x_4799_ == 0 {
                                                        v___y_4744_ = v___y_4759_;
                                                        v___y_4745_ = v_a_4787_;
                                                        v___y_4746_ = v_h_4758_;
                                                        state = 12;
                                                        continue;
                                                    } else {
                                                        v___x_4800_ =
                                                            l_Lake_Env_leanGithash(v_lakeEnv_4570_);
                                                        v___x_4801_ = lean_string_dec_eq(
                                                            v_leanHash_4792_,
                                                            v___x_4800_,
                                                        );
                                                        leanh::lean_dec_ref(v___x_4800_);
                                                        if v___x_4801_ == 0 {
                                                            v___y_4744_ = v___y_4759_;
                                                            v___y_4745_ = v_a_4787_;
                                                            v___y_4746_ = v_h_4758_;
                                                            state = 12;
                                                            continue;
                                                        } else {
                                                            leanh::lean_dec(v_a_4787_);
                                                            leanh::lean_dec_ref(v___x_4742_);
                                                            leanh::lean_dec_ref(v___x_4599_);
                                                            leanh::lean_dec(v_a_4593_);
                                                            leanh::lean_dec_ref(
                                                                v_configFile_4575_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_pkgDir_4574_,
                                                            );
                                                            leanh::lean_dec(v_pkgName_4573_);
                                                            leanh::lean_dec(v_pkgIdx_4572_);
                                                            leanh::lean_dec_ref(
                                                                v_lakeEnv_4570_,
                                                            );
                                                            v___x_4802_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_4596_, v_leanOpts_4577_);
                                                            leanh::lean_dec_ref(v___x_4596_);
                                                            if leanh::lean_obj_tag(
                                                                v___x_4802_,
                                                            ) == 0
                                                            {
                                                                v_a_4803_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_4802_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_4803_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_4802_,
                                                                    1,
                                                                );
                                                                v___x_4804_ =
                                                                    lean_io_prim_handle_unlock(
                                                                        v_h_4758_,
                                                                    );
                                                                leanh::lean_dec(v_h_4758_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_4804_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec_ref_known(v___x_4804_, 1);
                                                                    v___x_4805_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4805_,
                                                                        0,
                                                                        v_a_4803_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4805_,
                                                                        1,
                                                                        v___y_4759_,
                                                                    );
                                                                    return v___x_4805_;
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_a_4803_,
                                                                    );
                                                                    v_a_4806_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_4804_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v_a_4806_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v___x_4804_, 1);
                                                                    v___x_4807_ =
                                                                        lean_io_error_to_string(
                                                                            v_a_4806_,
                                                                        );
                                                                    v___x_4808_ = 3;
                                                                    v___x_4809_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4809_,
                                                                        0,
                                                                        v___x_4807_,
                                                                    );
                                                                    leanh::lean_ctor_set_uint8(v___x_4809_, (core::mem::size_of::<*mut leanh::LeanObject>()*1) as u32, v___x_4808_);
                                                                    v___x_4810_ =
                                                                        lean_array_get_size(
                                                                            v___y_4759_,
                                                                        );
                                                                    v___x_4811_ = lean_array_push(
                                                                        v___y_4759_,
                                                                        v___x_4809_,
                                                                    );
                                                                    v___x_4812_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4812_,
                                                                        0,
                                                                        v___x_4810_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4812_,
                                                                        1,
                                                                        v___x_4811_,
                                                                    );
                                                                    return v___x_4812_;
                                                                }
                                                            } else {
                                                                leanh::lean_dec(v_h_4758_);
                                                                v_a_4813_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_4802_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_4813_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_4802_,
                                                                    1,
                                                                );
                                                                v___x_4814_ =
                                                                    lean_io_error_to_string(
                                                                        v_a_4813_,
                                                                    );
                                                                v___x_4815_ = 3;
                                                                v___x_4816_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (1) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4816_,
                                                                    0,
                                                                    v___x_4814_,
                                                                );
                                                                leanh::lean_ctor_set_uint8(v___x_4816_, (core::mem::size_of::<*mut leanh::LeanObject>()*1) as u32, v___x_4815_);
                                                                v___x_4817_ = lean_array_get_size(
                                                                    v___y_4759_,
                                                                );
                                                                v___x_4818_ = lean_array_push(
                                                                    v___y_4759_,
                                                                    v___x_4816_,
                                                                );
                                                                v___x_4819_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        1,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4819_,
                                                                    0,
                                                                    v___x_4817_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4819_,
                                                                    1,
                                                                    v___x_4818_,
                                                                );
                                                                return v___x_4819_;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_h_4758_);
                            leanh::lean_dec_ref(v___x_4742_);
                            leanh::lean_dec_ref(v___x_4599_);
                            leanh::lean_dec_ref(v___x_4596_);
                            leanh::lean_dec(v_a_4593_);
                            leanh::lean_dec_ref(v_leanOpts_4577_);
                            leanh::lean_dec_ref(v_configFile_4575_);
                            leanh::lean_dec_ref(v_pkgDir_4574_);
                            leanh::lean_dec(v_pkgName_4573_);
                            leanh::lean_dec(v_pkgIdx_4572_);
                            leanh::lean_dec_ref(v_lakeEnv_4570_);
                            v_a_4820_ = leanh::lean_ctor_get(v___x_4761_, 0);
                            leanh::lean_inc(v_a_4820_);
                            leanh::lean_dec_ref_known(v___x_4761_, 1);
                            v___x_4821_ = lean_io_error_to_string(v_a_4820_);
                            v___x_4822_ = 3;
                            v___x_4823_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_4823_, 0, v___x_4821_);
                            leanh::lean_ctor_set_uint8(
                                v___x_4823_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_4822_,
                            );
                            v___x_4824_ = lean_array_get_size(v___y_4759_);
                            v___x_4825_ = lean_array_push(v___y_4759_, v___x_4823_);
                            v___x_4826_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4826_, 0, v___x_4824_);
                            leanh::lean_ctor_set(v___x_4826_, 1, v___x_4825_);
                            return v___x_4826_;
                        }
                    } else {
                        leanh::lean_dec(v_h_4758_);
                        leanh::lean_dec_ref(v___x_4742_);
                        leanh::lean_dec_ref(v___x_4599_);
                        leanh::lean_dec_ref(v___x_4596_);
                        leanh::lean_dec(v_a_4593_);
                        leanh::lean_dec_ref(v_leanOpts_4577_);
                        leanh::lean_dec_ref(v_configFile_4575_);
                        leanh::lean_dec_ref(v_pkgDir_4574_);
                        leanh::lean_dec(v_pkgName_4573_);
                        leanh::lean_dec(v_pkgIdx_4572_);
                        leanh::lean_dec_ref(v_lakeEnv_4570_);
                        v_a_4827_ = leanh::lean_ctor_get(v___x_4760_, 0);
                        leanh::lean_inc(v_a_4827_);
                        leanh::lean_dec_ref_known(v___x_4760_, 1);
                        v___x_4828_ = lean_io_error_to_string(v_a_4827_);
                        v___x_4829_ = 3;
                        v___x_4830_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_4830_, 0, v___x_4828_);
                        leanh::lean_ctor_set_uint8(
                            v___x_4830_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_4829_,
                        );
                        v___x_4831_ = lean_array_get_size(v___y_4759_);
                        v___x_4832_ = lean_array_push(v___y_4759_, v___x_4830_);
                        v___x_4833_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4833_, 0, v___x_4831_);
                        leanh::lean_ctor_set(v___x_4833_, 1, v___x_4832_);
                        return v___x_4833_;
                    }
                } else {
                    v___x_4834_ =
                        l_Lake_importConfigFile___lam__0(v___x_4742_, v___x_4599_, v_h_4758_);
                    leanh::lean_dec(v_h_4758_);
                    leanh::lean_dec_ref(v___x_4742_);
                    if leanh::lean_obj_tag(v___x_4834_) == 0 {
                        v_a_4835_ = leanh::lean_ctor_get(v___x_4834_, 0);
                        leanh::lean_inc(v_a_4835_);
                        leanh::lean_dec_ref_known(v___x_4834_, 1);
                        v_h_4601_ = v_a_4835_;
                        v_lakeOpts_4602_ = v_lakeOpts_4576_;
                        v___y_4603_ = v___y_4759_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_4599_);
                        leanh::lean_dec_ref(v___x_4596_);
                        leanh::lean_dec(v_a_4593_);
                        leanh::lean_dec_ref(v_leanOpts_4577_);
                        leanh::lean_dec(v_lakeOpts_4576_);
                        leanh::lean_dec_ref(v_configFile_4575_);
                        leanh::lean_dec_ref(v_pkgDir_4574_);
                        leanh::lean_dec(v_pkgName_4573_);
                        leanh::lean_dec(v_pkgIdx_4572_);
                        leanh::lean_dec_ref(v_lakeEnv_4570_);
                        v_a_4836_ = leanh::lean_ctor_get(v___x_4834_, 0);
                        leanh::lean_inc(v_a_4836_);
                        leanh::lean_dec_ref_known(v___x_4834_, 1);
                        v___x_4837_ = lean_io_error_to_string(v_a_4836_);
                        v___x_4838_ = 3;
                        v___x_4839_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_4839_, 0, v___x_4837_);
                        leanh::lean_ctor_set_uint8(
                            v___x_4839_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_4838_,
                        );
                        v___x_4840_ = lean_array_get_size(v___y_4759_);
                        v___x_4841_ = lean_array_push(v___y_4759_, v___x_4839_);
                        v___x_4842_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4842_, 0, v___x_4840_);
                        leanh::lean_ctor_set(v___x_4842_, 1, v___x_4841_);
                        return v___x_4842_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_importConfigFile___boxed(
    mut v_cfg_4905_: *mut leanh::LeanObject,
    mut v_a_4906_: *mut leanh::LeanObject,
    mut v_a_4907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4908_ = l_Lake_importConfigFile(v_cfg_4905_, v_a_4906_);
    return v_res_4908_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Lean_Elab(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Load_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Frontend(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache);
    leanh::lean_dec_ref(res);
    l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts =
        _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts();
    leanh::lean_mark_persistent(
        l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Lean_Elab(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Lean_Elab(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Load_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Frontend(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Extensions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_AttributesCore(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Lean_Elab(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Lean_Elab(builtin);
}