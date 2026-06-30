// Lean compiler output
// Module: LeanIR
// Imports: Init Init Lean.CoreM Lean.Util.ForEachExpr Lean.Util.Path Lean.Environment Lean.Compiler.Options Lean.Compiler.IR.CompilerM Lean.Compiler.CSimpAttr Lean.Compiler.LCNF.EmitRust Lean.Language.Lean Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.Main
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_display_cumulative_profiling_times, lean_get_ir_extra_const_names, lean_get_stderr,
    lean_io_get_num_heartbeats, lean_io_prim_handle_mk, lean_io_prim_handle_write,
    lean_ir_export_entries, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_shiftr, lean_nat_sub, lean_panic_fn_borrowed, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq, lean_string_memcmp,
    lean_string_push, lean_string_to_utf8, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Hashable::l_String_instHashableRaw_hash;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toName;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_firstFrontendMacroScope,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IO::l_instInhabitedEIO___aux__1___boxed;
use crate::r#gen::Init::System::IOError::{
    l_instInhabitedError, lean_io_error_to_string, lean_mk_io_user_error,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::{initialize_Init, runtime_initialize_Init};
use crate::r#gen::Lean::Class::{l_Lean_classExtension, l_Lean_instInhabitedClassState_default};
use crate::r#gen::Lean::Compiler::CSimpAttr::{
    initialize_Lean_Compiler_CSimpAttr, l_Lean_Compiler_CSimp_ext,
    l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg,
    l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16,
    l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg,
    runtime_initialize_Lean_Compiler_CSimpAttr,
};
use crate::r#gen::Lean::Compiler::ExternAttr::l_Lean_isExtern;
use crate::r#gen::Lean::Compiler::IR::Basic::l_Lean_IR_Decl_name;
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, l_Lean_IR_declMapExt,
    runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::EmitRust::{
    initialize_Lean_Compiler_LCNF_EmitRust, l_Lean_Compiler_LCNF_emitRust,
    runtime_initialize_Lean_Compiler_LCNF_EmitRust,
};
use crate::r#gen::Lean::Compiler::LCNF::Main::{
    initialize_Lean_Compiler_LCNF_Main, l_Lean_Compiler_LCNF_postponedCompileDeclsExt,
    l_Lean_Compiler_LCNF_resumeCompilation, runtime_initialize_Lean_Compiler_LCNF_Main,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_impureSigExt,
    runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::PublicDeclsExt::l_Lean_Compiler_LCNF_setDeclPublic;
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_inLeanIR,
    runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::{
    initialize_Lean_CoreM, l_Lean_Core_getAndEmptyMessageLog___redArg,
    l_Lean_Core_getMaxHeartbeats, l_Lean_diagnostics, l_Lean_maxHeartbeats,
    runtime_initialize_Lean_CoreM,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, l_Lean_getOptionDecls};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_isEmpty___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_instInhabited, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::{
    l_Lean_FileMap_toPosition, l_Lean_instInhabitedFileMap_default,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_mkMessageCore;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_setState___redArg;
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment,
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_IO_println___at___00Lean_Environment_displayStats_spec__1,
    l_Lean_EnvExtension_setState___redArg, l_Lean_Environment_displayStats,
    l_Lean_Environment_getModuleIdx_x3f, l_Lean_Environment_header, l_Lean_Environment_mainModule,
    l_Lean_Environment_setMainModule, l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
    l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg, l_Lean_finalizeImport,
    l_Lean_importModulesCore, l_Lean_instDecidableEqOLeanLevel,
    l_Lean_instInhabitedImportState_default,
    l_Lean_instInhabitedPersistentEnvExtensionState___redArg, l_Lean_instOrdOLeanLevel_ord,
    l_Lean_mkModuleData, l_Lean_saveModuleData, runtime_initialize_Lean_Environment,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::ImportingFlag::l_Lean_withImporting___boxed;
use crate::r#gen::Lean::Language::Lean::{
    initialize_Lean_Language_Lean, l_Lean_Language_Lean_setOption,
    runtime_initialize_Lean_Language_Lean,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_Message_toString, l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_nil, l_Lean_MessageData_ofFormat, l_Lean_MessageData_toString,
    l_Lean_MessageLog_add, l_Lean_MessageLog_hasErrors, l_Lean_instBEqMessageSeverity_beq,
};
use crate::r#gen::Lean::Meta::Instances::l_Lean_Meta_instanceExtension;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_Extension_extension, l_Lean_Meta_Match_Extension_instInhabitedState,
};
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_ScopedEnvExtension_instInhabitedStateStack_default;
use crate::r#gen::Lean::Setup::l_Lean_ModuleSetup_load;
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
use crate::r#gen::Lean::Util::LeanOptions::l_Lean_LeanOptions_toOptions;
use crate::r#gen::Lean::Util::Path::{
    initialize_Lean_Util_Path, l_Lean_getBuildDir, l_Lean_initSearchPath,
    runtime_initialize_Lean_Util_Path,
};
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::{
    l_Lean_inheritedTraceOptions, l_Lean_trace_profiler_output, l_Lean_trace_profiler_serve,
};
pub static l___private_LeanIR_0__mkIRData___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l___private_LeanIR_0__mkIRData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__mkIRData___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_LeanIR_0__mkIRData___closed__1_value: leanh::LeanArrayObject<0> =
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
static mut l___private_LeanIR_0__mkIRData___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__mkIRData___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 68, 0]};
static mut l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_LeanIR_0__setConfigOption___closed__0_value: leanh::LeanStringObject<
    17,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 111, 112, 116, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_LeanIR_0__setConfigOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__setConfigOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_LeanIR_0__setConfigOption___closed__1_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_LeanIR_0__setConfigOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__setConfigOption___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_LeanIR_0__setConfigOption___closed__2_value: leanh::LeanStringObject<
    48,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_LeanIR_0__setConfigOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__setConfigOption___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_LeanIR_0__setConfigOption___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_LeanIR_0__setConfigOption___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_LeanIR_0__setConfigOption___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__setConfigOption___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_LeanIR_0__setConfigOption___closed__4_value: leanh::LeanStringObject<
    28,
> = leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 116, 114, 97, 105, 108, 105, 110, 103, 32, 97, 114,
        103, 117, 109, 101, 110, 116, 32, 96, 0,
    ],
};
static mut l___private_LeanIR_0__setConfigOption___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__setConfigOption___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_LeanIR_0__setConfigOption___closed__5_value: leanh::LeanStringObject<
    45,
> = leanh::LeanStringObject {
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
        96, 44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 114, 103, 117, 109, 101, 110,
        116, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 45, 68, 111, 112,
        116, 61, 118, 97, 108, 96, 0,
    ],
};
static mut l___private_LeanIR_0__setConfigOption___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_LeanIR_0__setConfigOption___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_panic___at___00main_spec__5___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00main_spec__5___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0: u64 =
    0;
pub static l_main___lam__1___closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110,
            32, 35, 0,
        ],
    };
static mut l_main___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [95, 98, 111, 120, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value:
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
    m_data: [45, 45, 115, 116, 97, 116, 0],
};
static mut l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__0_value: leanh::LeanStringObject<75> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 75,
        m_capacity: 75,
        m_length: 74,
        m_data: [
            117, 115, 97, 103, 101, 58, 32, 108, 101, 97, 110, 105, 114, 32, 60, 115, 101, 116,
            117, 112, 46, 106, 115, 111, 110, 62, 32, 60, 111, 117, 116, 112, 117, 116, 46, 105,
            114, 62, 32, 60, 111, 117, 116, 112, 117, 116, 46, 114, 115, 62, 32, 91, 45, 45, 115,
            116, 97, 116, 93, 32, 60, 45, 68, 111, 112, 116, 61, 118, 97, 108, 62, 46, 46, 46, 0,
        ],
    };
static mut l_main___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__0_value) as *mut leanh::LeanObject;
pub static l_main___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_main___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__1_value) as *mut leanh::LeanObject;
pub static l_main___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_main___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__2_value) as *mut leanh::LeanObject;
static mut l_main___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_main___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__10_value) as *mut leanh::LeanObject;
pub static l_main___closed__11_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [105, 114, 0],
    };
static mut l_main___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__11_value) as *mut leanh::LeanObject;
pub static l_main___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_main___closed__11_value) as *mut leanh::LeanObject,
            6135693438932418717 as *mut leanh::LeanObject,
        ],
    };
static mut l_main___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__12_value) as *mut leanh::LeanObject;
pub static l_main___closed__13_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            82, 117, 115, 116, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105,
            111, 110, 0,
        ],
    };
static mut l_main___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__13_value) as *mut leanh::LeanObject;
static mut l_main___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__15_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_main___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__15_value) as *mut leanh::LeanObject;
pub static l_main___closed__16_value: leanh::LeanStringObject<7> =
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
        m_data: [76, 101, 97, 110, 73, 82, 0],
    };
static mut l_main___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__16_value) as *mut leanh::LeanObject;
pub static l_main___closed__17_value: leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 105, 110, 0],
    };
static mut l_main___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__17_value) as *mut leanh::LeanObject;
pub static l_main___closed__18_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_main___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__18_value) as *mut leanh::LeanObject;
static mut l_main___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__20_value: leanh::LeanStringObject<7> =
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
        m_data: [105, 109, 112, 111, 114, 116, 0],
    };
static mut l_main___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__20_value) as *mut leanh::LeanObject;
static mut l_main___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__23_value: leanh::LeanStringObject<6> =
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
        m_data: [95, 117, 110, 105, 113, 0],
    };
static mut l_main___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__23_value) as *mut leanh::LeanObject;
pub static l_main___closed__24_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_main___closed__23_value) as *mut leanh::LeanObject,
            3978731030111751661 as *mut leanh::LeanObject,
        ],
    };
static mut l_main___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__24_value) as *mut leanh::LeanObject;
pub static l_main___closed__25_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_main___closed__24_value) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_main___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__25_value) as *mut leanh::LeanObject;
static mut l_main___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__28_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__28: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__29_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__29: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__30_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__30: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_main___closed__31_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__31: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__32_value: leanh::LeanArrayObject<0> =
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
static mut l_main___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__32_value) as *mut leanh::LeanObject;
pub static l_main___closed__33_value: leanh::LeanArrayObject<0> =
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
static mut l_main___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__33_value) as *mut leanh::LeanObject;
pub static l_main___closed__34_value: leanh::LeanStringObject<9> =
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
        m_data: [109, 111, 100, 117, 108, 101, 32, 39, 0],
    };
static mut l_main___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__34_value) as *mut leanh::LeanObject;
pub static l_main___closed__35_value: leanh::LeanStringObject<12> =
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
        m_data: [39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0],
    };
static mut l_main___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__35_value) as *mut leanh::LeanObject;
static mut l_main___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__36: u8 = 0;
pub static mut l_main___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_main___boxed__const__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(
    mut v_a_3741_: *mut leanh::LeanObject,
    mut v_as_3742_: *mut leanh::LeanObject,
    mut v_i_3743_: usize,
    mut v_stop_3744_: usize,
) -> u8 {
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: usize = 0;
    let mut v___x_3749_: usize = 0;
    let mut v___x_3751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3745_ = lean_usize_dec_eq(v_i_3743_, v_stop_3744_);
                if v___x_3745_ == 0 {
                    v___x_3746_ = lean_array_uget_borrowed(v_as_3742_, v_i_3743_);
                    v___x_3747_ = lean_name_eq(v_a_3741_, v___x_3746_);
                    if v___x_3747_ == 0 {
                        v___x_3748_ = 1usize;
                        v___x_3749_ = lean_usize_add(v_i_3743_, v___x_3748_);
                        v_i_3743_ = v___x_3749_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3747_;
                    }
                } else {
                    v___x_3751_ = 0;
                    return v___x_3751_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1___boxed(
    mut v_a_3752_: *mut leanh::LeanObject,
    mut v_as_3753_: *mut leanh::LeanObject,
    mut v_i_3754_: *mut leanh::LeanObject,
    mut v_stop_3755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3756_: usize = 0;
    let mut v_stop_boxed_3757_: usize = 0;
    let mut v_res_3758_: u8 = 0;
    let mut v_r_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3756_ = leanh::lean_unbox_usize(v_i_3754_);
    leanh::lean_dec(v_i_3754_);
    v_stop_boxed_3757_ = leanh::lean_unbox_usize(v_stop_3755_);
    leanh::lean_dec(v_stop_3755_);
    v_res_3758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_3752_, v_as_3753_, v_i_boxed_3756_, v_stop_boxed_3757_);
    leanh::lean_dec_ref(v_as_3753_);
    leanh::lean_dec(v_a_3752_);
    v_r_3759_ = leanh::lean_box((v_res_3758_) as usize);
    return v_r_3759_;
}
pub unsafe fn l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(
    mut v_as_3760_: *mut leanh::LeanObject,
    mut v_a_3761_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: u8 = 0;
    v___x_3762_ = leanh::lean_unsigned_to_nat(0);
    v___x_3763_ = lean_array_get_size(v_as_3760_);
    v___x_3764_ = lean_nat_dec_lt(v___x_3762_, v___x_3763_);
    if v___x_3764_ == 0 {
        return v___x_3764_;
    } else {
        if v___x_3764_ == 0 {
            return v___x_3764_;
        } else {
            let mut v___x_3765_: usize = 0;
            let mut v___x_3766_: usize = 0;
            let mut v___x_3767_: u8 = 0;
            v___x_3765_ = 0usize;
            v___x_3766_ = lean_usize_of_nat(v___x_3763_);
            v___x_3767_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_3761_, v_as_3760_, v___x_3765_, v___x_3766_);
            return v___x_3767_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(
    mut v_as_3768_: *mut leanh::LeanObject,
    mut v_a_3769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3770_: u8 = 0;
    let mut v_r_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3770_ =
        l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_as_3768_, v_a_3769_);
    leanh::lean_dec(v_a_3769_);
    leanh::lean_dec_ref(v_as_3768_);
    v_r_3771_ = leanh::lean_box((v_res_3770_) as usize);
    return v_r_3771_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(
    mut v_irExtNames_3772_: *mut leanh::LeanObject,
    mut v_as_3773_: *mut leanh::LeanObject,
    mut v_i_3774_: usize,
    mut v_stop_3775_: usize,
    mut v_b_3776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: usize = 0;
    let mut v___x_3780_: usize = 0;
    let mut v___x_3782_: u8 = 0;
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3782_ = lean_usize_dec_eq(v_i_3774_, v_stop_3775_);
                if v___x_3782_ == 0 {
                    v___x_3783_ = lean_array_uget_borrowed(v_as_3773_, v_i_3774_);
                    v_fst_3784_ = leanh::lean_ctor_get(v___x_3783_, 0);
                    v___x_3785_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(
                        v_irExtNames_3772_,
                        v_fst_3784_,
                    );
                    if v___x_3785_ == 0 {
                        leanh::lean_inc(v___x_3783_);
                        v___x_3786_ = lean_array_push(v_b_3776_, v___x_3783_);
                        v___y_3778_ = v___x_3786_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3778_ = v_b_3776_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3776_;
                }
            }
            1 => {
                v___x_3779_ = 1usize;
                v___x_3780_ = lean_usize_add(v_i_3774_, v___x_3779_);
                v_i_3774_ = v___x_3780_;
                v_b_3776_ = v___y_3778_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(
    mut v_irExtNames_3787_: *mut leanh::LeanObject,
    mut v_as_3788_: *mut leanh::LeanObject,
    mut v_i_3789_: *mut leanh::LeanObject,
    mut v_stop_3790_: *mut leanh::LeanObject,
    mut v_b_3791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3792_: usize = 0;
    let mut v_stop_boxed_3793_: usize = 0;
    let mut v_res_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3792_ = leanh::lean_unbox_usize(v_i_3789_);
    leanh::lean_dec(v_i_3789_);
    v_stop_boxed_3793_ = leanh::lean_unbox_usize(v_stop_3790_);
    leanh::lean_dec(v_stop_3790_);
    v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_3787_, v_as_3788_, v_i_boxed_3792_, v_stop_boxed_3793_, v_b_3791_);
    leanh::lean_dec_ref(v_as_3788_);
    leanh::lean_dec_ref(v_irExtNames_3787_);
    return v_res_3794_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(
    mut v_sz_3795_: usize,
    mut v_i_3796_: usize,
    mut v_bs_3797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3798_: u8 = 0;
    let mut v_v_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: usize = 0;
    let mut v___x_3804_: usize = 0;
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3798_ = lean_usize_dec_lt(v_i_3796_, v_sz_3795_);
                if v___x_3798_ == 0 {
                    return v_bs_3797_;
                } else {
                    v_v_3799_ = lean_array_uget_borrowed(v_bs_3797_, v_i_3796_);
                    v_fst_3800_ = leanh::lean_ctor_get(v_v_3799_, 0);
                    leanh::lean_inc(v_fst_3800_);
                    v___x_3801_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3802_ = lean_array_uset(v_bs_3797_, v_i_3796_, v___x_3801_);
                    v___x_3803_ = 1usize;
                    v___x_3804_ = lean_usize_add(v_i_3796_, v___x_3803_);
                    v___x_3805_ = lean_array_uset(v_bs_x27_3802_, v_i_3796_, v_fst_3800_);
                    v_i_3796_ = v___x_3804_;
                    v_bs_3797_ = v___x_3805_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(
    mut v_sz_3807_: *mut leanh::LeanObject,
    mut v_i_3808_: *mut leanh::LeanObject,
    mut v_bs_3809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3810_: usize = 0;
    let mut v_i_boxed_3811_: usize = 0;
    let mut v_res_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3810_ = leanh::lean_unbox_usize(v_sz_3807_);
    leanh::lean_dec(v_sz_3807_);
    v_i_boxed_3811_ = leanh::lean_unbox_usize(v_i_3808_);
    leanh::lean_dec(v_i_3808_);
    v_res_3812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_boxed_3810_, v_i_boxed_3811_, v_bs_3809_);
    return v_res_3812_;
}
pub unsafe fn l___private_LeanIR_0__mkIRData(
    mut v_env_3817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_irEntries_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: u8 = 0;
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___y_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_3830_: u8 = 0;
    let mut v_imports_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v_sz_3845_: usize = 0;
    let mut v___x_3846_: usize = 0;
    let mut v_irExtNames_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: usize = 0;
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: usize = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref_n(v_env_3817_, 2);
                v_irEntries_3819_ = lean_ir_export_entries(v_env_3817_);
                v___x_3820_ = 2;
                v___x_3821_ = leanh::lean_box(0);
                v___x_3822_ = l_Lean_mkModuleData(v_env_3817_, v___x_3820_, v___x_3821_);
                if leanh::lean_obj_tag(v___x_3822_) == 0 {
                    v_a_3823_ = leanh::lean_ctor_get(v___x_3822_, 0);
                    v_isSharedCheck_3853_ = (!leanh::lean_is_exclusive(v___x_3822_)) as u8;
                    if v_isSharedCheck_3853_ == 0 {
                        v___x_3825_ = v___x_3822_;
                        v_isShared_3826_ = v_isSharedCheck_3853_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3823_);
                        leanh::lean_dec(v___x_3822_);
                        v___x_3825_ = leanh::lean_box(0);
                        v_isShared_3826_ = v_isSharedCheck_3853_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_irEntries_3819_);
                    leanh::lean_dec_ref(v_env_3817_);
                    return v___x_3822_;
                }
            }
            1 => {
                v_entries_3840_ = leanh::lean_ctor_get(v_a_3823_, 4);
                leanh::lean_inc_ref(v_entries_3840_);
                leanh::lean_dec(v_a_3823_);
                v___x_3841_ = leanh::lean_unsigned_to_nat(0);
                v___x_3842_ = lean_array_get_size(v_entries_3840_);
                v___x_3843_ = l___private_LeanIR_0__mkIRData___closed__1;
                v___x_3844_ = lean_nat_dec_lt(v___x_3841_, v___x_3842_);
                if v___x_3844_ == 0 {
                    leanh::lean_dec_ref(v_entries_3840_);
                    v___y_3828_ = v___x_3843_;
                    state = 2;
                    continue;
                } else {
                    v_sz_3845_ = lean_array_size(v_irEntries_3819_);
                    v___x_3846_ = 0usize;
                    leanh::lean_inc_ref(v_irEntries_3819_);
                    v_irExtNames_3847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_3845_, v___x_3846_, v_irEntries_3819_);
                    v___x_3848_ = lean_nat_dec_le(v___x_3842_, v___x_3842_);
                    if v___x_3848_ == 0 {
                        if v___x_3844_ == 0 {
                            leanh::lean_dec_ref(v_irExtNames_3847_);
                            leanh::lean_dec_ref(v_entries_3840_);
                            v___y_3828_ = v___x_3843_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3849_ = lean_usize_of_nat(v___x_3842_);
                            v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_3847_, v_entries_3840_, v___x_3846_, v___x_3849_, v___x_3843_);
                            leanh::lean_dec_ref(v_entries_3840_);
                            leanh::lean_dec_ref(v_irExtNames_3847_);
                            v___y_3828_ = v___x_3850_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3851_ = lean_usize_of_nat(v___x_3842_);
                        v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_3847_, v_entries_3840_, v___x_3846_, v___x_3851_, v___x_3843_);
                        leanh::lean_dec_ref(v_entries_3840_);
                        leanh::lean_dec_ref(v_irExtNames_3847_);
                        v___y_3828_ = v___x_3852_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3829_ = l_Lean_Environment_header(v_env_3817_);
                v_isModule_3830_ = leanh::lean_ctor_get_uint8(
                    v___x_3829_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                v_imports_3831_ = leanh::lean_ctor_get(v___x_3829_, 1);
                leanh::lean_inc_ref(v_imports_3831_);
                leanh::lean_dec_ref(v___x_3829_);
                v___x_3832_ = l___private_LeanIR_0__mkIRData___closed__0;
                v___x_3833_ = 1;
                v___x_3834_ = lean_get_ir_extra_const_names(v_env_3817_, v___x_3820_, v___x_3833_);
                v___x_3835_ = l_Array_append___redArg(v_irEntries_3819_, v___y_3828_);
                leanh::lean_dec_ref(v___y_3828_);
                v___x_3836_ = leanh::lean_alloc_ctor(0, 5, (1) as u32);
                leanh::lean_ctor_set(v___x_3836_, 0, v_imports_3831_);
                leanh::lean_ctor_set(v___x_3836_, 1, v___x_3832_);
                leanh::lean_ctor_set(v___x_3836_, 2, v___x_3832_);
                leanh::lean_ctor_set(v___x_3836_, 3, v___x_3834_);
                leanh::lean_ctor_set(v___x_3836_, 4, v___x_3835_);
                leanh::lean_ctor_set_uint8(
                    v___x_3836_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v_isModule_3830_,
                );
                if v_isShared_3826_ == 0 {
                    leanh::lean_ctor_set(v___x_3825_, 0, v___x_3836_);
                    v___x_3838_ = v___x_3825_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
                    v___x_3838_ = v_reuseFailAlloc_3839_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_LeanIR_0__mkIRData___boxed(
    mut v_env_3854_: *mut leanh::LeanObject,
    mut v_a_3855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3856_ = l___private_LeanIR_0__mkIRData(v_env_3854_);
    return v_res_3856_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0;
    v___x_3859_ = lean_string_utf8_byte_size(v___x_3858_);
    return v___x_3859_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(
    mut v_s_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    v___x_3861_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0;
    v___x_3862_ = lean_string_utf8_byte_size(v_s_3860_);
    v___x_3863_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1_once), _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1);
    v___x_3864_ = lean_nat_dec_le(v___x_3863_, v___x_3862_);
    if v___x_3864_ == 0 {
        let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_3860_);
        v___x_3865_ = leanh::lean_box(0);
        return v___x_3865_;
    } else {
        let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3867_: u8 = 0;
        v___x_3866_ = leanh::lean_unsigned_to_nat(0);
        v___x_3867_ = lean_string_memcmp(
            v_s_3860_,
            v___x_3861_,
            v___x_3866_,
            v___x_3866_,
            v___x_3863_,
        );
        if v___x_3867_ == 0 {
            let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_3860_);
            v___x_3868_ = leanh::lean_box(0);
            return v___x_3868_;
        } else {
            let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_3860_);
            v___x_3869_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_3869_, 0, v_s_3860_);
            leanh::lean_ctor_set(v___x_3869_, 1, v___x_3866_);
            leanh::lean_ctor_set(v___x_3869_, 2, v___x_3862_);
            v___x_3870_ = l_String_Slice_pos_x21(v___x_3869_, v___x_3863_);
            leanh::lean_dec_ref_known(v___x_3869_, 3);
            v___x_3871_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_3871_, 0, v_s_3860_);
            leanh::lean_ctor_set(v___x_3871_, 1, v___x_3870_);
            leanh::lean_ctor_set(v___x_3871_, 2, v___x_3862_);
            v___x_3872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3872_, 0, v___x_3871_);
            return v___x_3872_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(
    mut v_s_3873_: *mut leanh::LeanObject,
    mut v_pat_3874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ =
        l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(
            v_s_3873_,
        );
    return v___x_3875_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(
    mut v_s_3876_: *mut leanh::LeanObject,
    mut v_pat_3877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3878_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(
        v_s_3876_,
        v_pat_3877_,
    );
    leanh::lean_dec_ref(v_pat_3877_);
    return v_res_3878_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(
    mut v_val_3879_: *mut leanh::LeanObject,
    mut v_a_3880_: *mut leanh::LeanObject,
    mut v_b_3881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: u8 = 0;
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u32 = 0;
    let mut v___x_3889_: u32 = 0;
    let mut v___x_3890_: u8 = 0;
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3882_ = leanh::lean_ctor_get(v_val_3879_, 0);
                v_startInclusive_3883_ = leanh::lean_ctor_get(v_val_3879_, 1);
                v_endExclusive_3884_ = leanh::lean_ctor_get(v_val_3879_, 2);
                v___x_3885_ = lean_nat_sub(v_endExclusive_3884_, v_startInclusive_3883_);
                v___x_3886_ = lean_nat_dec_eq(v_a_3880_, v___x_3885_);
                leanh::lean_dec(v___x_3885_);
                if v___x_3886_ == 0 {
                    v___x_3887_ = lean_nat_add(v_startInclusive_3883_, v_a_3880_);
                    v___x_3888_ = lean_string_utf8_get_fast(v_str_3882_, v___x_3887_);
                    v___x_3889_ = 61;
                    v___x_3890_ = lean_uint32_dec_eq(v___x_3888_, v___x_3889_);
                    if v___x_3890_ == 0 {
                        leanh::lean_dec(v_a_3880_);
                        v___x_3891_ = leanh::lean_box(0);
                        v___x_3892_ = lean_string_utf8_next_fast(v_str_3882_, v___x_3887_);
                        leanh::lean_dec(v___x_3887_);
                        v___x_3893_ = lean_nat_sub(v___x_3892_, v_startInclusive_3883_);
                        v_a_3880_ = v___x_3893_;
                        v_b_3881_ = v___x_3891_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3887_);
                        v___x_3895_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3895_, 0, v_a_3880_);
                        return v___x_3895_;
                    }
                } else {
                    leanh::lean_dec(v_a_3880_);
                    leanh::lean_inc(v_b_3881_);
                    return v_b_3881_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(
    mut v_val_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
    mut v_b_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3899_ =
        l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(
            v_val_3896_,
            v_a_3897_,
            v_b_3898_,
        );
    leanh::lean_dec(v_b_3898_);
    leanh::lean_dec_ref(v_val_3896_);
    return v_res_3899_;
}
pub unsafe fn l___private_LeanIR_0__setConfigOption(
    mut v_opts_3907_: *mut leanh::LeanObject,
    mut v_arg_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___y_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3929_: u8 = 0;
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: u8 = 0;
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_a_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3962_: u8 = 0;
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3967_: u8 = 0;
    let mut v_searcher_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_arg_3908_);
                v___x_3910_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_3908_);
                if leanh::lean_obj_tag(v___x_3910_) == 1 {
                    leanh::lean_dec_ref(v_arg_3908_);
                    v_val_3911_ = leanh::lean_ctor_get(v___x_3910_, 0);
                    v_isSharedCheck_3975_ = (!leanh::lean_is_exclusive(v___x_3910_)) as u8;
                    if v_isSharedCheck_3975_ == 0 {
                        v___x_3913_ = v___x_3910_;
                        v_isShared_3914_ = v_isSharedCheck_3975_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3911_);
                        leanh::lean_dec(v___x_3910_);
                        v___x_3913_ = leanh::lean_box(0);
                        v_isShared_3914_ = v_isSharedCheck_3975_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3910_);
                    leanh::lean_dec_ref(v_opts_3907_);
                    v___x_3976_ = l___private_LeanIR_0__setConfigOption___closed__4;
                    v___x_3977_ = lean_string_append(v___x_3976_, v_arg_3908_);
                    leanh::lean_dec_ref(v_arg_3908_);
                    v___x_3978_ = l___private_LeanIR_0__setConfigOption___closed__5;
                    v___x_3979_ = lean_string_append(v___x_3977_, v___x_3978_);
                    v___x_3980_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3980_, 0, v___x_3979_);
                    v___x_3981_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3981_, 0, v___x_3980_);
                    return v___x_3981_;
                }
            }
            1 => {
                v_searcher_3968_ = leanh::lean_unsigned_to_nat(0);
                v___x_3969_ = leanh::lean_box(0);
                v___x_3970_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_3911_, v_searcher_3968_, v___x_3969_);
                if leanh::lean_obj_tag(v___x_3970_) == 0 {
                    v_startInclusive_3971_ = leanh::lean_ctor_get(v_val_3911_, 1);
                    v_endExclusive_3972_ = leanh::lean_ctor_get(v_val_3911_, 2);
                    v___x_3973_ = lean_nat_sub(v_endExclusive_3972_, v_startInclusive_3971_);
                    v___y_3916_ = v___x_3973_;
                    state = 2;
                    continue;
                } else {
                    v_val_3974_ = leanh::lean_ctor_get(v___x_3970_, 0);
                    leanh::lean_inc(v_val_3974_);
                    leanh::lean_dec_ref_known(v___x_3970_, 1);
                    v___y_3916_ = v_val_3974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_str_3917_ = leanh::lean_ctor_get(v_val_3911_, 0);
                v_startInclusive_3918_ = leanh::lean_ctor_get(v_val_3911_, 1);
                v_endExclusive_3919_ = leanh::lean_ctor_get(v_val_3911_, 2);
                v_isSharedCheck_3967_ = (!leanh::lean_is_exclusive(v_val_3911_)) as u8;
                if v_isSharedCheck_3967_ == 0 {
                    v___x_3921_ = v_val_3911_;
                    v_isShared_3922_ = v_isSharedCheck_3967_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_3919_);
                    leanh::lean_inc(v_startInclusive_3918_);
                    leanh::lean_inc(v_str_3917_);
                    leanh::lean_dec(v_val_3911_);
                    v___x_3921_ = leanh::lean_box(0);
                    v_isShared_3922_ = v_isSharedCheck_3967_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3923_ = lean_nat_sub(v_endExclusive_3919_, v_startInclusive_3918_);
                v___x_3924_ = lean_nat_dec_eq(v___y_3916_, v___x_3923_);
                leanh::lean_dec(v___x_3923_);
                if v___x_3924_ == 0 {
                    v___x_3925_ = l_Lean_getOptionDecls();
                    if leanh::lean_obj_tag(v___x_3925_) == 0 {
                        v_a_3926_ = leanh::lean_ctor_get(v___x_3925_, 0);
                        v_isSharedCheck_3954_ =
                            (!leanh::lean_is_exclusive(v___x_3925_)) as u8;
                        if v_isSharedCheck_3954_ == 0 {
                            v___x_3928_ = v___x_3925_;
                            v_isShared_3929_ = v_isSharedCheck_3954_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3926_);
                            leanh::lean_dec(v___x_3925_);
                            v___x_3928_ = leanh::lean_box(0);
                            v_isShared_3929_ = v_isSharedCheck_3954_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3921_);
                        leanh::lean_dec(v_endExclusive_3919_);
                        leanh::lean_dec(v_startInclusive_3918_);
                        leanh::lean_dec_ref(v_str_3917_);
                        leanh::lean_dec(v___y_3916_);
                        leanh::lean_del_object(v___x_3913_);
                        leanh::lean_dec_ref(v_opts_3907_);
                        v_a_3955_ = leanh::lean_ctor_get(v___x_3925_, 0);
                        v_isSharedCheck_3962_ =
                            (!leanh::lean_is_exclusive(v___x_3925_)) as u8;
                        if v_isSharedCheck_3962_ == 0 {
                            v___x_3957_ = v___x_3925_;
                            v_isShared_3958_ = v_isSharedCheck_3962_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3955_);
                            leanh::lean_dec(v___x_3925_);
                            v___x_3957_ = leanh::lean_box(0);
                            v_isShared_3958_ = v_isSharedCheck_3962_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3921_);
                    leanh::lean_dec(v_endExclusive_3919_);
                    leanh::lean_dec(v_startInclusive_3918_);
                    leanh::lean_dec_ref(v_str_3917_);
                    leanh::lean_dec(v___y_3916_);
                    leanh::lean_dec_ref(v_opts_3907_);
                    v___x_3963_ = l___private_LeanIR_0__setConfigOption___closed__3;
                    if v_isShared_3914_ == 0 {
                        leanh::lean_ctor_set(v___x_3913_, 0, v___x_3963_);
                        v___x_3965_ = v___x_3913_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3963_);
                        v___x_3965_ = v_reuseFailAlloc_3966_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3930_ = lean_nat_add(v_startInclusive_3918_, v___y_3916_);
                leanh::lean_dec(v___y_3916_);
                leanh::lean_inc(v___x_3930_);
                leanh::lean_inc(v_startInclusive_3918_);
                leanh::lean_inc_ref(v_str_3917_);
                if v_isShared_3922_ == 0 {
                    leanh::lean_ctor_set(v___x_3921_, 2, v___x_3930_);
                    v___x_3932_ = v___x_3921_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_str_3917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_startInclusive_3918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 2, v___x_3930_);
                    v___x_3932_ = v_reuseFailAlloc_3953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_name_3933_ = l_String_Slice_toName(v___x_3932_);
                leanh::lean_dec_ref(v___x_3932_);
                v___x_3934_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3926_, v_name_3933_);
                leanh::lean_dec(v_a_3926_);
                if leanh::lean_obj_tag(v___x_3934_) == 1 {
                    leanh::lean_del_object(v___x_3928_);
                    leanh::lean_del_object(v___x_3913_);
                    v_val_3935_ = leanh::lean_ctor_get(v___x_3934_, 0);
                    leanh::lean_inc(v_val_3935_);
                    leanh::lean_dec_ref_known(v___x_3934_, 1);
                    v___x_3936_ = lean_string_utf8_next_fast(v_str_3917_, v___x_3930_);
                    leanh::lean_dec(v___x_3930_);
                    v___x_3937_ = lean_nat_sub(v___x_3936_, v_startInclusive_3918_);
                    v___x_3938_ = lean_nat_add(v_startInclusive_3918_, v___x_3937_);
                    leanh::lean_dec(v___x_3937_);
                    leanh::lean_dec(v_startInclusive_3918_);
                    v_val_3939_ =
                        lean_string_utf8_extract(v_str_3917_, v___x_3938_, v_endExclusive_3919_);
                    leanh::lean_dec(v_endExclusive_3919_);
                    leanh::lean_dec(v___x_3938_);
                    leanh::lean_dec_ref(v_str_3917_);
                    v___x_3940_ = l_Lean_Language_Lean_setOption(
                        v_opts_3907_,
                        v_val_3935_,
                        v_name_3933_,
                        v_val_3939_,
                    );
                    return v___x_3940_;
                } else {
                    leanh::lean_dec(v___x_3934_);
                    leanh::lean_dec(v___x_3930_);
                    leanh::lean_dec(v_endExclusive_3919_);
                    leanh::lean_dec(v_startInclusive_3918_);
                    leanh::lean_dec_ref(v_str_3917_);
                    leanh::lean_dec_ref(v_opts_3907_);
                    v___x_3941_ = l___private_LeanIR_0__setConfigOption___closed__0;
                    v___x_3942_ = 1;
                    v___x_3943_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_3933_,
                        v___x_3942_,
                    );
                    v___x_3944_ = lean_string_append(v___x_3941_, v___x_3943_);
                    leanh::lean_dec_ref(v___x_3943_);
                    v___x_3945_ = l___private_LeanIR_0__setConfigOption___closed__1;
                    v___x_3946_ = lean_string_append(v___x_3944_, v___x_3945_);
                    if v_isShared_3914_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3913_, 18);
                        leanh::lean_ctor_set(v___x_3913_, 0, v___x_3946_);
                        v___x_3948_ = v___x_3913_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3952_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3946_);
                        v___x_3948_ = v_reuseFailAlloc_3952_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3929_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3928_, 1);
                    leanh::lean_ctor_set(v___x_3928_, 0, v___x_3948_);
                    v___x_3950_ = v___x_3928_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3948_);
                    v___x_3950_ = v_reuseFailAlloc_3951_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3950_;
            }
            8 => {
                if v_isShared_3958_ == 0 {
                    v___x_3960_ = v___x_3957_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3961_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
                    v___x_3960_ = v_reuseFailAlloc_3961_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3960_;
            }
            10 => {
                return v___x_3965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_LeanIR_0__setConfigOption___boxed(
    mut v_opts_3982_: *mut leanh::LeanObject,
    mut v_arg_3983_: *mut leanh::LeanObject,
    mut v_a_3984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3985_ = l___private_LeanIR_0__setConfigOption(v_opts_3982_, v_arg_3983_);
    return v_res_3985_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(
    mut v_val_3986_: *mut leanh::LeanObject,
    mut v_inst_3987_: *mut leanh::LeanObject,
    mut v_R_3988_: *mut leanh::LeanObject,
    mut v_a_3989_: *mut leanh::LeanObject,
    mut v_b_3990_: *mut leanh::LeanObject,
    mut v_c_3991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ =
        l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(
            v_val_3986_,
            v_a_3989_,
            v_b_3990_,
        );
    return v___x_3992_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(
    mut v_val_3993_: *mut leanh::LeanObject,
    mut v_inst_3994_: *mut leanh::LeanObject,
    mut v_R_3995_: *mut leanh::LeanObject,
    mut v_a_3996_: *mut leanh::LeanObject,
    mut v_b_3997_: *mut leanh::LeanObject,
    mut v_c_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ =
        l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(
            v_val_3993_,
            v_inst_3994_,
            v_R_3995_,
            v_a_3996_,
            v_b_3997_,
            v_c_3998_,
        );
    leanh::lean_dec(v_b_3997_);
    leanh::lean_dec_ref(v_val_3993_);
    return v_res_3999_;
}
pub unsafe fn l_main___elam__0___redArg(
    mut v___x_4000_: *mut leanh::LeanObject,
    mut v_inst_4001_: *mut leanh::LeanObject,
    mut v_ext_4002_: *mut leanh::LeanObject,
    mut v_env_4003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toEnvExtension_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addImportedFn_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4013_: u8 = 0;
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4020_: u8 = 0;
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v_a_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4037_: u8 = 0;
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_unused_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEnvExtension_4005_ = leanh::lean_ctor_get(v_ext_4002_, 0);
                leanh::lean_inc_ref(v_toEnvExtension_4005_);
                v_addImportedFn_4006_ = leanh::lean_ctor_get(v_ext_4002_, 2);
                leanh::lean_inc_ref(v_addImportedFn_4006_);
                leanh::lean_dec_ref(v_ext_4002_);
                v_asyncMode_4007_ = leanh::lean_ctor_get(v_toEnvExtension_4005_, 2);
                v___x_4008_ =
                    l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_4001_);
                leanh::lean_inc_ref(v_env_4003_);
                v___x_4009_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_4008_,
                        v_toEnvExtension_4005_,
                        v_env_4003_,
                        v_asyncMode_4007_,
                        v___x_4000_,
                    );
                leanh::lean_dec_ref(v___x_4008_);
                v_importedEntries_4010_ = leanh::lean_ctor_get(v___x_4009_, 0);
                v_isSharedCheck_4038_ = (!leanh::lean_is_exclusive(v___x_4009_)) as u8;
                if v_isSharedCheck_4038_ == 0 {
                    v_unused_4039_ = leanh::lean_ctor_get(v___x_4009_, 1);
                    leanh::lean_dec(v_unused_4039_);
                    v___x_4012_ = v___x_4009_;
                    v_isShared_4013_ = v_isSharedCheck_4038_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_importedEntries_4010_);
                    leanh::lean_dec(v___x_4009_);
                    v___x_4012_ = leanh::lean_box(0);
                    v_isShared_4013_ = v_isSharedCheck_4038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4014_ = l_Lean_Options_empty;
                leanh::lean_inc_ref(v_env_4003_);
                v___x_4015_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4015_, 0, v_env_4003_);
                leanh::lean_ctor_set(v___x_4015_, 1, v___x_4014_);
                leanh::lean_inc_ref(v_importedEntries_4010_);
                v___x_4016_ = leanh::lean_apply_3(
                    v_addImportedFn_4006_,
                    v_importedEntries_4010_,
                    v___x_4015_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4016_) == 0 {
                    v_a_4017_ = leanh::lean_ctor_get(v___x_4016_, 0);
                    v_isSharedCheck_4029_ = (!leanh::lean_is_exclusive(v___x_4016_)) as u8;
                    if v_isSharedCheck_4029_ == 0 {
                        v___x_4019_ = v___x_4016_;
                        v_isShared_4020_ = v_isSharedCheck_4029_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4017_);
                        leanh::lean_dec(v___x_4016_);
                        v___x_4019_ = leanh::lean_box(0);
                        v_isShared_4020_ = v_isSharedCheck_4029_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4012_);
                    leanh::lean_dec_ref(v_importedEntries_4010_);
                    leanh::lean_dec_ref(v_toEnvExtension_4005_);
                    leanh::lean_dec_ref(v_env_4003_);
                    v_a_4030_ = leanh::lean_ctor_get(v___x_4016_, 0);
                    v_isSharedCheck_4037_ = (!leanh::lean_is_exclusive(v___x_4016_)) as u8;
                    if v_isSharedCheck_4037_ == 0 {
                        v___x_4032_ = v___x_4016_;
                        v_isShared_4033_ = v_isSharedCheck_4037_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4030_);
                        leanh::lean_dec(v___x_4016_);
                        v___x_4032_ = leanh::lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4037_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4013_ == 0 {
                    leanh::lean_ctor_set(v___x_4012_, 1, v_a_4017_);
                    v___x_4022_ = v___x_4012_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4028_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_importedEntries_4010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_a_4017_);
                    v___x_4022_ = v_reuseFailAlloc_4028_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4023_ = leanh::lean_box(0);
                v___x_4024_ = l_Lean_EnvExtension_setState___redArg(
                    v_toEnvExtension_4005_,
                    v_env_4003_,
                    v___x_4022_,
                    v___x_4023_,
                );
                if v_isShared_4020_ == 0 {
                    leanh::lean_ctor_set(v___x_4019_, 0, v___x_4024_);
                    v___x_4026_ = v___x_4019_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
                    v___x_4026_ = v_reuseFailAlloc_4027_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4026_;
            }
            5 => {
                if v_isShared_4033_ == 0 {
                    v___x_4035_ = v___x_4032_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4036_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
                    v___x_4035_ = v_reuseFailAlloc_4036_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_main___elam__0___redArg___boxed(
    mut v___x_4040_: *mut leanh::LeanObject,
    mut v_inst_4041_: *mut leanh::LeanObject,
    mut v_ext_4042_: *mut leanh::LeanObject,
    mut v_env_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4045_ = l_main___elam__0___redArg(v___x_4040_, v_inst_4041_, v_ext_4042_, v_env_4043_);
    return v_res_4045_;
}
pub unsafe fn l_main___elam__0(
    mut v___x_4046_: *mut leanh::LeanObject,
    mut v_00_u03b1_4047_: *mut leanh::LeanObject,
    mut v_00_u03b2_4048_: *mut leanh::LeanObject,
    mut v_00_u03c3_4049_: *mut leanh::LeanObject,
    mut v_inst_4050_: *mut leanh::LeanObject,
    mut v_ext_4051_: *mut leanh::LeanObject,
    mut v_env_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4054_ = l_main___elam__0___redArg(v___x_4046_, v_inst_4050_, v_ext_4051_, v_env_4052_);
    return v___x_4054_;
}
pub unsafe fn l_main___elam__0___boxed(
    mut v___x_4055_: *mut leanh::LeanObject,
    mut v_00_u03b1_4056_: *mut leanh::LeanObject,
    mut v_00_u03b2_4057_: *mut leanh::LeanObject,
    mut v_00_u03c3_4058_: *mut leanh::LeanObject,
    mut v_inst_4059_: *mut leanh::LeanObject,
    mut v_ext_4060_: *mut leanh::LeanObject,
    mut v_env_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4063_ = l_main___elam__0(
        v___x_4055_,
        v_00_u03b1_4056_,
        v_00_u03b2_4057_,
        v_00_u03c3_4058_,
        v_inst_4059_,
        v_ext_4060_,
        v_env_4061_,
    );
    return v_res_4063_;
}
pub unsafe fn _init_l_panic___at___00main_spec__5___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4064_ = l_instInhabitedError;
    v___x_4065_ = leanh::lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_4065_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4065_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4065_, 2, v___x_4064_);
    return v___x_4065_;
}
pub unsafe fn l_panic___at___00main_spec__5(
    mut v_msg_4066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_20091__overap_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4068_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00main_spec__5___closed__0),
        core::ptr::addr_of_mut!(l_panic___at___00main_spec__5___closed__0_once),
        _init_l_panic___at___00main_spec__5___closed__0,
    );
    v___x_20091__overap_4069_ = lean_panic_fn_borrowed(v___x_4068_, v_msg_4066_);
    v___x_4070_ = leanh::lean_apply_1(v___x_20091__overap_4069_, leanh::lean_box(0));
    return v___x_4070_;
}
pub unsafe fn l_panic___at___00main_spec__5___boxed(
    mut v_msg_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ = l_panic___at___00main_spec__5(v_msg_4071_);
    return v_res_4073_;
}
pub unsafe fn l_Lean_Option_get___at___00main_spec__8(
    mut v_opts_4074_: *mut leanh::LeanObject,
    mut v_opt_4075_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4076_ = leanh::lean_ctor_get(v_opt_4075_, 0);
    v_defValue_4077_ = leanh::lean_ctor_get(v_opt_4075_, 1);
    v_map_4078_ = leanh::lean_ctor_get(v_opts_4074_, 0);
    v___x_4079_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4078_,
            v_name_4076_,
        );
    if leanh::lean_obj_tag(v___x_4079_) == 0 {
        let mut v___x_4080_: u8 = 0;
        v___x_4080_ = (leanh::lean_unbox(v_defValue_4077_) as u8);
        return v___x_4080_;
    } else {
        let mut v_val_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4081_ = leanh::lean_ctor_get(v___x_4079_, 0);
        leanh::lean_inc(v_val_4081_);
        leanh::lean_dec_ref_known(v___x_4079_, 1);
        if leanh::lean_obj_tag(v_val_4081_) == 1 {
            let mut v_v_4082_: u8 = 0;
            v_v_4082_ = leanh::lean_ctor_get_uint8(v_val_4081_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_4081_, 0);
            return v_v_4082_;
        } else {
            let mut v___x_4083_: u8 = 0;
            leanh::lean_dec(v_val_4081_);
            v___x_4083_ = (leanh::lean_unbox(v_defValue_4077_) as u8);
            return v___x_4083_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00main_spec__8___boxed(
    mut v_opts_4084_: *mut leanh::LeanObject,
    mut v_opt_4085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4086_: u8 = 0;
    let mut v_r_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ = l_Lean_Option_get___at___00main_spec__8(v_opts_4084_, v_opt_4085_);
    leanh::lean_dec_ref(v_opt_4085_);
    leanh::lean_dec_ref(v_opts_4084_);
    v_r_4087_ = leanh::lean_box((v_res_4086_) as usize);
    return v_r_4087_;
}
pub unsafe fn l_Lean_Option_get___at___00main_spec__9(
    mut v_opts_4088_: *mut leanh::LeanObject,
    mut v_opt_4089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4090_ = leanh::lean_ctor_get(v_opt_4089_, 0);
    v_defValue_4091_ = leanh::lean_ctor_get(v_opt_4089_, 1);
    v_map_4092_ = leanh::lean_ctor_get(v_opts_4088_, 0);
    v___x_4093_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4092_,
            v_name_4090_,
        );
    if leanh::lean_obj_tag(v___x_4093_) == 0 {
        leanh::lean_inc(v_defValue_4091_);
        return v_defValue_4091_;
    } else {
        let mut v_val_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4094_ = leanh::lean_ctor_get(v___x_4093_, 0);
        leanh::lean_inc(v_val_4094_);
        leanh::lean_dec_ref_known(v___x_4093_, 1);
        if leanh::lean_obj_tag(v_val_4094_) == 3 {
            let mut v_v_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_4095_ = leanh::lean_ctor_get(v_val_4094_, 0);
            leanh::lean_inc(v_v_4095_);
            leanh::lean_dec_ref_known(v_val_4094_, 1);
            return v_v_4095_;
        } else {
            leanh::lean_dec(v_val_4094_);
            leanh::lean_inc(v_defValue_4091_);
            return v_defValue_4091_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00main_spec__9___boxed(
    mut v_opts_4096_: *mut leanh::LeanObject,
    mut v_opt_4097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4098_ = l_Lean_Option_get___at___00main_spec__9(v_opts_4096_, v_opt_4097_);
    leanh::lean_dec_ref(v_opt_4097_);
    leanh::lean_dec_ref(v_opts_4096_);
    return v_res_4098_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(
    mut v___x_4099_: *mut leanh::LeanObject,
    mut v_a_4100_: *mut leanh::LeanObject,
    mut v_x_4101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4107_: u8 = 0;
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEffectiveImport_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parts_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irData_x3f_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needsIRTrans_4117_: u8 = 0;
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v_hasData_4121_: u8 = 0;
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v_module_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: u8 = 0;
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_unused_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v_unused_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4101_) == 0 {
                    leanh::lean_dec(v_a_4100_);
                    return v_x_4101_;
                } else {
                    v_key_4102_ = leanh::lean_ctor_get(v_x_4101_, 0);
                    v_value_4103_ = leanh::lean_ctor_get(v_x_4101_, 1);
                    v_tail_4104_ = leanh::lean_ctor_get(v_x_4101_, 2);
                    v_isSharedCheck_4151_ = (!leanh::lean_is_exclusive(v_x_4101_)) as u8;
                    if v_isSharedCheck_4151_ == 0 {
                        v___x_4106_ = v_x_4101_;
                        v_isShared_4107_ = v_isSharedCheck_4151_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4104_);
                        leanh::lean_inc(v_value_4103_);
                        leanh::lean_inc(v_key_4102_);
                        leanh::lean_dec(v_x_4101_);
                        v___x_4106_ = leanh::lean_box(0);
                        v_isShared_4107_ = v_isSharedCheck_4151_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4108_ = lean_name_eq(v_key_4102_, v_a_4100_);
                if v___x_4108_ == 0 {
                    v___x_4109_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_4099_, v_a_4100_, v_tail_4104_);
                    if v_isShared_4107_ == 0 {
                        leanh::lean_ctor_set(v___x_4106_, 2, v___x_4109_);
                        v___x_4111_ = v___x_4106_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4112_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_key_4102_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_value_4103_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 2, v___x_4109_);
                        v___x_4111_ = v_reuseFailAlloc_4112_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_4102_);
                    v_toEffectiveImport_4113_ = leanh::lean_ctor_get(v_value_4103_, 0);
                    leanh::lean_inc_ref(v_toEffectiveImport_4113_);
                    v_toImport_4114_ = leanh::lean_ctor_get(v_toEffectiveImport_4113_, 0);
                    leanh::lean_inc_ref(v_toImport_4114_);
                    v_parts_4115_ = leanh::lean_ctor_get(v_value_4103_, 1);
                    v_irData_x3f_4116_ = leanh::lean_ctor_get(v_value_4103_, 2);
                    v_needsIRTrans_4117_ = leanh::lean_ctor_get_uint8(
                        v_value_4103_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_isSharedCheck_4149_ = (!leanh::lean_is_exclusive(v_value_4103_)) as u8;
                    if v_isSharedCheck_4149_ == 0 {
                        v_unused_4150_ = leanh::lean_ctor_get(v_value_4103_, 0);
                        leanh::lean_dec(v_unused_4150_);
                        v___x_4119_ = v_value_4103_;
                        v_isShared_4120_ = v_isSharedCheck_4149_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_irData_x3f_4116_);
                        leanh::lean_inc(v_parts_4115_);
                        leanh::lean_dec(v_value_4103_);
                        v___x_4119_ = leanh::lean_box(0);
                        v_isShared_4120_ = v_isSharedCheck_4149_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4111_;
            }
            3 => {
                v_hasData_4121_ = leanh::lean_ctor_get_uint8(
                    v_toEffectiveImport_4113_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_isSharedCheck_4147_ =
                    (!leanh::lean_is_exclusive(v_toEffectiveImport_4113_)) as u8;
                if v_isSharedCheck_4147_ == 0 {
                    v_unused_4148_ = leanh::lean_ctor_get(v_toEffectiveImport_4113_, 0);
                    leanh::lean_dec(v_unused_4148_);
                    v___x_4123_ = v_toEffectiveImport_4113_;
                    v_isShared_4124_ = v_isSharedCheck_4147_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_toEffectiveImport_4113_);
                    v___x_4123_ = leanh::lean_box(0);
                    v_isShared_4124_ = v_isSharedCheck_4147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_module_4125_ = leanh::lean_ctor_get(v_toImport_4114_, 0);
                v___x_4126_ = lean_name_eq(v_module_4125_, v___x_4099_);
                if v___x_4126_ == 0 {
                    v___x_4127_ = 2;
                    if v_isShared_4124_ == 0 {
                        v___x_4129_ = v___x_4123_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4136_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_toImport_4114_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4136_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                            v_hasData_4121_,
                        );
                        v___x_4129_ = v_reuseFailAlloc_4136_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_4137_ = 0;
                    if v_isShared_4124_ == 0 {
                        v___x_4139_ = v___x_4123_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4146_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_toImport_4114_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4146_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                            v_hasData_4121_,
                        );
                        v___x_4139_ = v_reuseFailAlloc_4146_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4129_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4127_,
                );
                if v_isShared_4120_ == 0 {
                    leanh::lean_ctor_set(v___x_4119_, 0, v___x_4129_);
                    v___x_4131_ = v___x_4119_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_parts_4115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 2, v_irData_x3f_4116_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4135_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_needsIRTrans_4117_,
                    );
                    v___x_4131_ = v_reuseFailAlloc_4135_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4107_ == 0 {
                    leanh::lean_ctor_set(v___x_4106_, 1, v___x_4131_);
                    leanh::lean_ctor_set(v___x_4106_, 0, v_a_4100_);
                    v___x_4133_ = v___x_4106_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 1, v___x_4131_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_tail_4104_);
                    v___x_4133_ = v_reuseFailAlloc_4134_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4133_;
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4139_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4137_,
                );
                if v_isShared_4120_ == 0 {
                    leanh::lean_ctor_set(v___x_4119_, 0, v___x_4139_);
                    v___x_4141_ = v___x_4119_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4145_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_parts_4115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 2, v_irData_x3f_4116_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4145_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_needsIRTrans_4117_,
                    );
                    v___x_4141_ = v_reuseFailAlloc_4145_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4107_ == 0 {
                    leanh::lean_ctor_set(v___x_4106_, 1, v___x_4141_);
                    leanh::lean_ctor_set(v___x_4106_, 0, v_a_4100_);
                    v___x_4143_ = v___x_4106_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4144_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4144_, 1, v___x_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4144_, 2, v_tail_4104_);
                    v___x_4143_ = v_reuseFailAlloc_4144_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5___boxed(
    mut v___x_4152_: *mut leanh::LeanObject,
    mut v_a_4153_: *mut leanh::LeanObject,
    mut v_x_4154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4155_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_4152_, v_a_4153_, v_x_4154_);
    leanh::lean_dec(v___x_4152_);
    return v_res_4155_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0()
-> u64 {
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u64 = 0;
    v___x_4156_ = leanh::lean_unsigned_to_nat(1723);
    v___x_4157_ = lean_uint64_of_nat(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(
    mut v___x_4158_: *mut leanh::LeanObject,
    mut v_m_4159_: *mut leanh::LeanObject,
    mut v_a_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4165_: u64 = 0;
    let mut v___x_4166_: u64 = 0;
    let mut v___x_4167_: u64 = 0;
    let mut v_fold_4168_: u64 = 0;
    let mut v___x_4169_: u64 = 0;
    let mut v___x_4170_: u64 = 0;
    let mut v___x_4171_: u64 = 0;
    let mut v___x_4172_: usize = 0;
    let mut v___x_4173_: usize = 0;
    let mut v___x_4174_: usize = 0;
    let mut v___x_4175_: usize = 0;
    let mut v___x_4176_: usize = 0;
    let mut v_bucket_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: u8 = 0;
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4181_: u8 = 0;
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bucket_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4189_: u8 = 0;
    let mut v_unused_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: u64 = 0;
    let mut v_hash_4193_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4161_ = leanh::lean_ctor_get(v_m_4159_, 0);
                v_buckets_4162_ = leanh::lean_ctor_get(v_m_4159_, 1);
                v___x_4163_ = lean_array_get_size(v_buckets_4162_);
                if leanh::lean_obj_tag(v_a_4160_) == 0 {
                    v___x_4192_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0);
                    v___y_4165_ = v___x_4192_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4193_ = leanh::lean_ctor_get_uint64(
                        v_a_4160_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4165_ = v_hash_4193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4166_ = 32u64;
                v___x_4167_ = lean_uint64_shift_right(v___y_4165_, v___x_4166_);
                v_fold_4168_ = lean_uint64_xor(v___y_4165_, v___x_4167_);
                v___x_4169_ = 16u64;
                v___x_4170_ = lean_uint64_shift_right(v_fold_4168_, v___x_4169_);
                v___x_4171_ = lean_uint64_xor(v_fold_4168_, v___x_4170_);
                v___x_4172_ = lean_uint64_to_usize(v___x_4171_);
                v___x_4173_ = lean_usize_of_nat(v___x_4163_);
                v___x_4174_ = 1usize;
                v___x_4175_ = lean_usize_sub(v___x_4173_, v___x_4174_);
                v___x_4176_ = lean_usize_land(v___x_4172_, v___x_4175_);
                v_bucket_4177_ = lean_array_uget_borrowed(v_buckets_4162_, v___x_4176_);
                v___x_4178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_4160_, v_bucket_4177_);
                if v___x_4178_ == 0 {
                    leanh::lean_dec(v_a_4160_);
                    return v_m_4159_;
                } else {
                    leanh::lean_inc(v_bucket_4177_);
                    leanh::lean_inc_ref(v_buckets_4162_);
                    leanh::lean_inc(v_size_4161_);
                    v_isSharedCheck_4189_ = (!leanh::lean_is_exclusive(v_m_4159_)) as u8;
                    if v_isSharedCheck_4189_ == 0 {
                        v_unused_4190_ = leanh::lean_ctor_get(v_m_4159_, 1);
                        leanh::lean_dec(v_unused_4190_);
                        v_unused_4191_ = leanh::lean_ctor_get(v_m_4159_, 0);
                        leanh::lean_dec(v_unused_4191_);
                        v___x_4180_ = v_m_4159_;
                        v_isShared_4181_ = v_isSharedCheck_4189_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_4159_);
                        v___x_4180_ = leanh::lean_box(0);
                        v_isShared_4181_ = v_isSharedCheck_4189_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4182_ = leanh::lean_box(0);
                v_buckets_4183_ = lean_array_uset(v_buckets_4162_, v___x_4176_, v___x_4182_);
                v_bucket_4184_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_4158_, v_a_4160_, v_bucket_4177_);
                v___x_4185_ = lean_array_uset(v_buckets_4183_, v___x_4176_, v_bucket_4184_);
                if v_isShared_4181_ == 0 {
                    leanh::lean_ctor_set(v___x_4180_, 1, v___x_4185_);
                    v___x_4187_ = v___x_4180_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4188_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_size_4161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4188_, 1, v___x_4185_);
                    v___x_4187_ = v_reuseFailAlloc_4188_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___boxed(
    mut v___x_4194_: *mut leanh::LeanObject,
    mut v_m_4195_: *mut leanh::LeanObject,
    mut v_a_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(
        v___x_4194_,
        v_m_4195_,
        v_a_4196_,
    );
    leanh::lean_dec(v___x_4194_);
    return v_res_4197_;
}
pub unsafe fn l_main___lam__0(
    mut v___x_4198_: *mut leanh::LeanObject,
    mut v___x_4199_: *mut leanh::LeanObject,
    mut v___x_4200_: u8,
    mut v___x_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: u8,
    mut v_name_4203_: *mut leanh::LeanObject,
    mut v___x_4204_: *mut leanh::LeanObject,
    mut v___x_4205_: u8,
    mut v___x_4206_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleNameMap_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleNames_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4215_: u8 = 0;
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: u32 = 0;
    let mut v___x_4220_: u8 = 0;
    let mut v___x_4221_: u8 = 0;
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4225_: u8 = 0;
    let mut v_a_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4208_ = lean_st_mk_ref(v___x_4198_);
                v___x_4209_ = l_Lean_importModulesCore(
                    v___x_4199_,
                    v___x_4200_,
                    v___x_4201_,
                    v___y_4202_,
                    v___x_4208_,
                );
                if leanh::lean_obj_tag(v___x_4209_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4209_, 1);
                    v___x_4210_ = lean_st_ref_get(v___x_4208_);
                    leanh::lean_dec(v___x_4208_);
                    v_moduleNameMap_4211_ = leanh::lean_ctor_get(v___x_4210_, 0);
                    v_moduleNames_4212_ = leanh::lean_ctor_get(v___x_4210_, 1);
                    v_isSharedCheck_4225_ = (!leanh::lean_is_exclusive(v___x_4210_)) as u8;
                    if v_isSharedCheck_4225_ == 0 {
                        v___x_4214_ = v___x_4210_;
                        v_isShared_4215_ = v_isSharedCheck_4225_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_moduleNames_4212_);
                        leanh::lean_inc(v_moduleNameMap_4211_);
                        leanh::lean_dec(v___x_4210_);
                        v___x_4214_ = leanh::lean_box(0);
                        v_isShared_4215_ = v_isSharedCheck_4225_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4208_);
                    leanh::lean_dec_ref(v___x_4204_);
                    leanh::lean_dec(v_name_4203_);
                    leanh::lean_dec_ref(v___x_4199_);
                    v_a_4226_ = leanh::lean_ctor_get(v___x_4209_, 0);
                    v_isSharedCheck_4233_ = (!leanh::lean_is_exclusive(v___x_4209_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4228_ = v___x_4209_;
                        v_isShared_4229_ = v_isSharedCheck_4233_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4226_);
                        leanh::lean_dec(v___x_4209_);
                        v___x_4228_ = leanh::lean_box(0);
                        v_isShared_4229_ = v_isSharedCheck_4233_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_name_4203_);
                v___x_4216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(
                    v_name_4203_,
                    v_moduleNameMap_4211_,
                    v_name_4203_,
                );
                leanh::lean_dec(v_name_4203_);
                if v_isShared_4215_ == 0 {
                    leanh::lean_ctor_set(v___x_4214_, 0, v___x_4216_);
                    v___x_4218_ = v___x_4214_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_moduleNames_4212_);
                    v___x_4218_ = v_reuseFailAlloc_4224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4219_ = 0;
                v___x_4220_ = 0;
                v___x_4221_ = l_Lean_instDecidableEqOLeanLevel(v___x_4220_, v___x_4200_);
                if v___x_4221_ == 0 {
                    v___x_4222_ = l_Lean_finalizeImport(
                        v___x_4218_,
                        v___x_4199_,
                        v___x_4204_,
                        v___x_4219_,
                        v___x_4205_,
                        v___x_4206_,
                        v___x_4220_,
                        v___x_4205_,
                    );
                    leanh::lean_dec_ref(v___x_4218_);
                    return v___x_4222_;
                } else {
                    v___x_4223_ = l_Lean_finalizeImport(
                        v___x_4218_,
                        v___x_4199_,
                        v___x_4204_,
                        v___x_4219_,
                        v___x_4205_,
                        v___x_4206_,
                        v___x_4220_,
                        v___x_4206_,
                    );
                    leanh::lean_dec_ref(v___x_4218_);
                    return v___x_4223_;
                }
            }
            3 => {
                if v_isShared_4229_ == 0 {
                    v___x_4231_ = v___x_4228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
                    v___x_4231_ = v_reuseFailAlloc_4232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_main___lam__0___boxed(
    mut v___x_4234_: *mut leanh::LeanObject,
    mut v___x_4235_: *mut leanh::LeanObject,
    mut v___x_4236_: *mut leanh::LeanObject,
    mut v___x_4237_: *mut leanh::LeanObject,
    mut v___y_4238_: *mut leanh::LeanObject,
    mut v_name_4239_: *mut leanh::LeanObject,
    mut v___x_4240_: *mut leanh::LeanObject,
    mut v___x_4241_: *mut leanh::LeanObject,
    mut v___x_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_36246__boxed_4244_: u8 = 0;
    let mut v___y_36248__boxed_4245_: u8 = 0;
    let mut v___x_36250__boxed_4246_: u8 = 0;
    let mut v___x_36251__boxed_4247_: u8 = 0;
    let mut v_res_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36246__boxed_4244_ = (leanh::lean_unbox(v___x_4236_) as u8);
    v___y_36248__boxed_4245_ = (leanh::lean_unbox(v___y_4238_) as u8);
    v___x_36250__boxed_4246_ = (leanh::lean_unbox(v___x_4241_) as u8);
    v___x_36251__boxed_4247_ = (leanh::lean_unbox(v___x_4242_) as u8);
    v_res_4248_ = l_main___lam__0(
        v___x_4234_,
        v___x_4235_,
        v___x_36246__boxed_4244_,
        v___x_4237_,
        v___y_36248__boxed_4245_,
        v_name_4239_,
        v___x_4240_,
        v___x_36250__boxed_4246_,
        v___x_36251__boxed_4247_,
    );
    return v_res_4248_;
}
pub unsafe fn l_main___lam__1(
    mut v___x_4250_: *mut leanh::LeanObject,
    mut v___x_4251_: *mut leanh::LeanObject,
    mut v___x_4252_: *mut leanh::LeanObject,
    mut v_name_4253_: *mut leanh::LeanObject,
    mut v_a_4254_: *mut leanh::LeanObject,
    mut v___x_4255_: *mut leanh::LeanObject,
    mut v_head_4256_: *mut leanh::LeanObject,
    mut v___x_4257_: *mut leanh::LeanObject,
    mut v___x_4258_: *mut leanh::LeanObject,
    mut v___x_4259_: *mut leanh::LeanObject,
    mut v___x_4260_: *mut leanh::LeanObject,
    mut v___x_4261_: *mut leanh::LeanObject,
    mut v___x_4262_: *mut leanh::LeanObject,
    mut v___x_4263_: *mut leanh::LeanObject,
    mut v___x_4264_: *mut leanh::LeanObject,
    mut v___x_4265_: u8,
    mut v___x_4266_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    let mut v_fileName_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4287_: u8 = 0;
    let mut v_inheritedTraceOptions_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v_msg_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4316_: u8 = 0;
    let mut v___y_4318_: u8 = 0;
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4330_: u8 = 0;
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut v_unused_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4268_ = lean_io_get_num_heartbeats();
                v___x_4269_ = lean_st_mk_ref(v___x_4250_);
                v___x_4270_ = lean_st_ref_get(v___x_4251_);
                v___x_4271_ = lean_st_ref_get(v___x_4269_);
                v_env_4272_ = leanh::lean_ctor_get(v___x_4271_, 0);
                leanh::lean_inc_ref(v_env_4272_);
                leanh::lean_dec(v___x_4271_);
                v___x_4273_ = l_Lean_diagnostics;
                v___x_4274_ = l_Lean_Option_get___at___00main_spec__8(v___x_4252_, v___x_4273_);
                v___x_4338_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4272_);
                leanh::lean_dec_ref(v_env_4272_);
                if v___x_4338_ == 0 {
                    if v___x_4274_ == 0 {
                        v___y_4318_ = v___x_4266_;
                        state = 5;
                        continue;
                    } else {
                        v___y_4318_ = v___x_4338_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_4318_ = v___x_4274_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_4290_ = l_Lean_maxRecDepth;
                v___x_4291_ = l_Lean_Option_get___at___00main_spec__9(v___x_4252_, v___x_4290_);
                v___x_4292_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4292_, 0, v_fileName_4276_);
                leanh::lean_ctor_set(v___x_4292_, 1, v_fileMap_4277_);
                leanh::lean_ctor_set(v___x_4292_, 2, v___x_4252_);
                leanh::lean_ctor_set(v___x_4292_, 3, v_currRecDepth_4278_);
                leanh::lean_ctor_set(v___x_4292_, 4, v___x_4291_);
                leanh::lean_ctor_set(v___x_4292_, 5, v_ref_4279_);
                leanh::lean_ctor_set(v___x_4292_, 6, v_currNamespace_4280_);
                leanh::lean_ctor_set(v___x_4292_, 7, v_openDecls_4281_);
                leanh::lean_ctor_set(v___x_4292_, 8, v_initHeartbeats_4282_);
                leanh::lean_ctor_set(v___x_4292_, 9, v_maxHeartbeats_4283_);
                leanh::lean_ctor_set(v___x_4292_, 10, v_quotContext_4284_);
                leanh::lean_ctor_set(v___x_4292_, 11, v_currMacroScope_4285_);
                leanh::lean_ctor_set(v___x_4292_, 12, v_cancelTk_x3f_4286_);
                leanh::lean_ctor_set(v___x_4292_, 13, v_inheritedTraceOptions_4288_);
                leanh::lean_ctor_set_uint8(
                    v___x_4292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_4274_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4287_,
                );
                v___x_4293_ = l_Lean_Compiler_LCNF_emitRust(v_name_4253_, v___x_4292_, v___y_4289_);
                leanh::lean_dec(v___y_4289_);
                leanh::lean_dec_ref_known(v___x_4292_, 14);
                if leanh::lean_obj_tag(v___x_4293_) == 0 {
                    v_a_4294_ = leanh::lean_ctor_get(v___x_4293_, 0);
                    leanh::lean_inc(v_a_4294_);
                    leanh::lean_dec_ref_known(v___x_4293_, 1);
                    v___x_4295_ = lean_st_ref_get(v___x_4269_);
                    leanh::lean_dec(v___x_4269_);
                    leanh::lean_dec(v___x_4295_);
                    v___x_4296_ = lean_string_to_utf8(v_a_4294_);
                    leanh::lean_dec(v_a_4294_);
                    v___x_4297_ = lean_io_prim_handle_write(v_a_4254_, v___x_4296_);
                    leanh::lean_dec_ref(v___x_4296_);
                    return v___x_4297_;
                } else {
                    leanh::lean_dec(v___x_4269_);
                    v_a_4298_ = leanh::lean_ctor_get(v___x_4293_, 0);
                    v_isSharedCheck_4316_ = (!leanh::lean_is_exclusive(v___x_4293_)) as u8;
                    if v_isSharedCheck_4316_ == 0 {
                        v___x_4300_ = v___x_4293_;
                        v_isShared_4301_ = v_isSharedCheck_4316_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4298_);
                        leanh::lean_dec(v___x_4293_);
                        v___x_4300_ = leanh::lean_box(0);
                        v_isShared_4301_ = v_isSharedCheck_4316_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4298_) == 0 {
                    v_msg_4302_ = leanh::lean_ctor_get(v_a_4298_, 1);
                    leanh::lean_inc_ref(v_msg_4302_);
                    leanh::lean_dec_ref_known(v_a_4298_, 2);
                    v___x_4303_ = l_Lean_MessageData_toString(v_msg_4302_);
                    v___x_4304_ = lean_mk_io_user_error(v___x_4303_);
                    if v_isShared_4301_ == 0 {
                        leanh::lean_ctor_set(v___x_4300_, 0, v___x_4304_);
                        v___x_4306_ = v___x_4300_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
                        v___x_4306_ = v_reuseFailAlloc_4307_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_id_4308_ = leanh::lean_ctor_get(v_a_4298_, 0);
                    leanh::lean_inc(v_id_4308_);
                    leanh::lean_dec_ref_known(v_a_4298_, 2);
                    v___x_4309_ = l_main___lam__1___closed__0;
                    v___x_4310_ = l_Nat_reprFast(v_id_4308_);
                    v___x_4311_ = lean_string_append(v___x_4309_, v___x_4310_);
                    leanh::lean_dec_ref(v___x_4310_);
                    v___x_4312_ = lean_mk_io_user_error(v___x_4311_);
                    if v_isShared_4301_ == 0 {
                        leanh::lean_ctor_set(v___x_4300_, 0, v___x_4312_);
                        v___x_4314_ = v___x_4300_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4315_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
                        v___x_4314_ = v_reuseFailAlloc_4315_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4306_;
            }
            4 => {
                return v___x_4314_;
            }
            5 => {
                if v___y_4318_ == 0 {
                    v___x_4319_ = lean_st_ref_take(v___x_4269_);
                    v_env_4320_ = leanh::lean_ctor_get(v___x_4319_, 0);
                    v_nextMacroScope_4321_ = leanh::lean_ctor_get(v___x_4319_, 1);
                    v_ngen_4322_ = leanh::lean_ctor_get(v___x_4319_, 2);
                    v_auxDeclNGen_4323_ = leanh::lean_ctor_get(v___x_4319_, 3);
                    v_traceState_4324_ = leanh::lean_ctor_get(v___x_4319_, 4);
                    v_messages_4325_ = leanh::lean_ctor_get(v___x_4319_, 6);
                    v_infoState_4326_ = leanh::lean_ctor_get(v___x_4319_, 7);
                    v_snapshotTasks_4327_ = leanh::lean_ctor_get(v___x_4319_, 8);
                    v_isSharedCheck_4336_ = (!leanh::lean_is_exclusive(v___x_4319_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v_unused_4337_ = leanh::lean_ctor_get(v___x_4319_, 5);
                        leanh::lean_dec(v_unused_4337_);
                        v___x_4329_ = v___x_4319_;
                        v_isShared_4330_ = v_isSharedCheck_4336_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4327_);
                        leanh::lean_inc(v_infoState_4326_);
                        leanh::lean_inc(v_messages_4325_);
                        leanh::lean_inc(v_traceState_4324_);
                        leanh::lean_inc(v_auxDeclNGen_4323_);
                        leanh::lean_inc(v_ngen_4322_);
                        leanh::lean_inc(v_nextMacroScope_4321_);
                        leanh::lean_inc(v_env_4320_);
                        leanh::lean_dec(v___x_4319_);
                        v___x_4329_ = leanh::lean_box(0);
                        v_isShared_4330_ = v_isSharedCheck_4336_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4255_);
                    leanh::lean_inc(v___x_4269_);
                    leanh::lean_inc(v___x_4260_);
                    v_fileName_4276_ = v_head_4256_;
                    v_fileMap_4277_ = v___x_4257_;
                    v_currRecDepth_4278_ = v___x_4258_;
                    v_ref_4279_ = v___x_4259_;
                    v_currNamespace_4280_ = v___x_4260_;
                    v_openDecls_4281_ = v___x_4261_;
                    v_initHeartbeats_4282_ = v___x_4268_;
                    v_maxHeartbeats_4283_ = v___x_4262_;
                    v_quotContext_4284_ = v___x_4260_;
                    v_currMacroScope_4285_ = v___x_4263_;
                    v_cancelTk_x3f_4286_ = v___x_4264_;
                    v_suppressElabErrors_4287_ = v___x_4265_;
                    v_inheritedTraceOptions_4288_ = v___x_4270_;
                    v___y_4289_ = v___x_4269_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_4331_ = l_Lean_Kernel_enableDiag(v_env_4320_, v___x_4274_);
                if v_isShared_4330_ == 0 {
                    leanh::lean_ctor_set(v___x_4329_, 5, v___x_4255_);
                    leanh::lean_ctor_set(v___x_4329_, 0, v___x_4331_);
                    v___x_4333_ = v___x_4329_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4335_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 1, v_nextMacroScope_4321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 2, v_ngen_4322_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 3, v_auxDeclNGen_4323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 4, v_traceState_4324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 5, v___x_4255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 6, v_messages_4325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 7, v_infoState_4326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 8, v_snapshotTasks_4327_);
                    v___x_4333_ = v_reuseFailAlloc_4335_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4334_ = lean_st_ref_set(v___x_4269_, v___x_4333_);
                leanh::lean_inc(v___x_4269_);
                leanh::lean_inc(v___x_4260_);
                v_fileName_4276_ = v_head_4256_;
                v_fileMap_4277_ = v___x_4257_;
                v_currRecDepth_4278_ = v___x_4258_;
                v_ref_4279_ = v___x_4259_;
                v_currNamespace_4280_ = v___x_4260_;
                v_openDecls_4281_ = v___x_4261_;
                v_initHeartbeats_4282_ = v___x_4268_;
                v_maxHeartbeats_4283_ = v___x_4262_;
                v_quotContext_4284_ = v___x_4260_;
                v_currMacroScope_4285_ = v___x_4263_;
                v_cancelTk_x3f_4286_ = v___x_4264_;
                v_suppressElabErrors_4287_ = v___x_4265_;
                v_inheritedTraceOptions_4288_ = v___x_4270_;
                v___y_4289_ = v___x_4269_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_main___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4339_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_4340_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_4341_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_name_4342_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_4343_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_4344_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_head_4345_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_4346_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_4347_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_4348_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_4349_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_4350_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_4351_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_4352_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_4353_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_4354_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___x_4355_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4356_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_36336__boxed_4357_: u8 = 0;
    let mut v___x_36337__boxed_4358_: u8 = 0;
    let mut v_res_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36336__boxed_4357_ = (leanh::lean_unbox(v___x_4354_) as u8);
    v___x_36337__boxed_4358_ = (leanh::lean_unbox(v___x_4355_) as u8);
    v_res_4359_ = l_main___lam__1(
        v___x_4339_,
        v___x_4340_,
        v___x_4341_,
        v_name_4342_,
        v_a_4343_,
        v___x_4344_,
        v_head_4345_,
        v___x_4346_,
        v___x_4347_,
        v___x_4348_,
        v___x_4349_,
        v___x_4350_,
        v___x_4351_,
        v___x_4352_,
        v___x_4353_,
        v___x_36336__boxed_4357_,
        v___x_36337__boxed_4358_,
    );
    leanh::lean_dec(v_a_4343_);
    leanh::lean_dec(v___x_4340_);
    return v_res_4359_;
}
pub unsafe fn l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(
    mut v_s_4360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = lean_get_stderr();
    v_putStr_4363_ = leanh::lean_ctor_get(v___x_4362_, 4);
    leanh::lean_inc_ref(v_putStr_4363_);
    leanh::lean_dec_ref(v___x_4362_);
    v___x_4364_ = leanh::lean_apply_2(v_putStr_4363_, v_s_4360_, leanh::lean_box(0));
    return v___x_4364_;
}
pub unsafe fn l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(
    mut v_s_4365_: *mut leanh::LeanObject,
    mut v_a_4366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4367_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_4365_);
    return v_res_4367_;
}
pub unsafe fn l_IO_eprintln___at___00main_spec__6(
    mut v_s_4368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4370_: u32 = 0;
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4370_ = 10;
    v___x_4371_ = lean_string_push(v_s_4368_, v___x_4370_);
    v___x_4372_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_4371_);
    return v___x_4372_;
}
pub unsafe fn l_IO_eprintln___at___00main_spec__6___boxed(
    mut v_s_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l_IO_eprintln___at___00main_spec__6(v_s_4373_);
    return v_res_4375_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(
    mut v_o_4379_: *mut leanh::LeanObject,
    mut v_k_4380_: *mut leanh::LeanObject,
    mut v_v_4381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4383_: u8 = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4386_: u8 = 0;
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: u8 = 0;
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4382_ = leanh::lean_ctor_get(v_o_4379_, 0);
                v_hasTrace_4383_ = leanh::lean_ctor_get_uint8(
                    v_o_4379_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4397_ = (!leanh::lean_is_exclusive(v_o_4379_)) as u8;
                if v_isSharedCheck_4397_ == 0 {
                    v___x_4385_ = v_o_4379_;
                    v_isShared_4386_ = v_isSharedCheck_4397_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_4382_);
                    leanh::lean_dec(v_o_4379_);
                    v___x_4385_ = leanh::lean_box(0);
                    v_isShared_4386_ = v_isSharedCheck_4397_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4387_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4387_, 0, v_v_4381_);
                leanh::lean_inc(v_k_4380_);
                v___x_4388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4380_, v___x_4387_, v_map_4382_);
                if v_hasTrace_4383_ == 0 {
                    v___x_4389_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1;
                    v___x_4390_ = l_Lean_Name_isPrefixOf(v___x_4389_, v_k_4380_);
                    leanh::lean_dec(v_k_4380_);
                    if v_isShared_4386_ == 0 {
                        leanh::lean_ctor_set(v___x_4385_, 0, v___x_4388_);
                        v___x_4392_ = v___x_4385_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4393_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4388_);
                        v___x_4392_ = v_reuseFailAlloc_4393_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_4380_);
                    if v_isShared_4386_ == 0 {
                        leanh::lean_ctor_set(v___x_4385_, 0, v___x_4388_);
                        v___x_4395_ = v___x_4385_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4396_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4388_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4396_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4383_,
                        );
                        v___x_4395_ = v_reuseFailAlloc_4396_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4392_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4390_,
                );
                return v___x_4392_;
            }
            3 => {
                return v___x_4395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_set___at___00main_spec__3(
    mut v_opts_4398_: *mut leanh::LeanObject,
    mut v_opt_4399_: *mut leanh::LeanObject,
    mut v_val_4400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4401_ = leanh::lean_ctor_get(v_opt_4399_, 0);
    leanh::lean_inc(v_name_4401_);
    leanh::lean_dec_ref(v_opt_4399_);
    v___x_4402_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(
        v_opts_4398_,
        v_name_4401_,
        v_val_4400_,
    );
    return v___x_4402_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(
    mut v___y_4404_: *mut leanh::LeanObject,
    mut v_as_4405_: *mut leanh::LeanObject,
    mut v_i_4406_: usize,
    mut v_stop_4407_: usize,
    mut v_b_4408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: usize = 0;
    let mut v___x_4412_: usize = 0;
    let mut v___x_4414_: u8 = 0;
    let mut v_fst_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut v_unused_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4414_ = lean_usize_dec_eq(v_i_4406_, v_stop_4407_);
                if v___x_4414_ == 0 {
                    v_fst_4415_ = leanh::lean_ctor_get(v_b_4408_, 0);
                    v_snd_4416_ = leanh::lean_ctor_get(v_b_4408_, 1);
                    v___x_4417_ = lean_array_uget_borrowed(v_as_4405_, v_i_4406_);
                    v___x_4418_ = l_Lean_IR_Decl_name(v___x_4417_);
                    if leanh::lean_obj_tag(v___x_4418_) == 1 {
                        v_pre_4433_ = leanh::lean_ctor_get(v___x_4418_, 0);
                        leanh::lean_inc(v_pre_4433_);
                        v_str_4434_ = leanh::lean_ctor_get(v___x_4418_, 1);
                        leanh::lean_inc_ref(v_str_4434_);
                        v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0;
                        v___x_4436_ = lean_string_dec_eq(v_str_4434_, v___x_4435_);
                        leanh::lean_dec_ref(v_str_4434_);
                        if v___x_4436_ == 0 {
                            leanh::lean_dec(v_pre_4433_);
                            leanh::lean_inc_ref(v___x_4418_);
                            v___y_4420_ = v___x_4418_;
                            state = 2;
                            continue;
                        } else {
                            v___y_4420_ = v_pre_4433_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v___x_4418_);
                        v___y_4420_ = v___x_4418_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4404_);
                    return v_b_4408_;
                }
            }
            1 => {
                v___x_4411_ = 1usize;
                v___x_4412_ = lean_usize_add(v_i_4406_, v___x_4411_);
                v_i_4406_ = v___x_4412_;
                v_b_4408_ = v___y_4410_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc_ref(v___y_4404_);
                v___x_4421_ = l_Lean_isExtern(v___y_4404_, v___y_4420_);
                if v___x_4421_ == 0 {
                    leanh::lean_dec(v___x_4418_);
                    v___y_4410_ = v_b_4408_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4416_);
                    leanh::lean_inc(v_fst_4415_);
                    v_isSharedCheck_4430_ = (!leanh::lean_is_exclusive(v_b_4408_)) as u8;
                    if v_isSharedCheck_4430_ == 0 {
                        v_unused_4431_ = leanh::lean_ctor_get(v_b_4408_, 1);
                        leanh::lean_dec(v_unused_4431_);
                        v_unused_4432_ = leanh::lean_ctor_get(v_b_4408_, 0);
                        leanh::lean_dec(v_unused_4432_);
                        v___x_4423_ = v_b_4408_;
                        v_isShared_4424_ = v_isSharedCheck_4430_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_b_4408_);
                        v___x_4423_ = leanh::lean_box(0);
                        v_isShared_4424_ = v_isSharedCheck_4430_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc_n(v___x_4417_, 2);
                v___x_4425_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4425_, 0, v___x_4417_);
                leanh::lean_ctor_set(v___x_4425_, 1, v_fst_4415_);
                v___x_4426_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_4416_, v___x_4418_, v___x_4417_);
                if v_isShared_4424_ == 0 {
                    leanh::lean_ctor_set(v___x_4423_, 1, v___x_4426_);
                    leanh::lean_ctor_set(v___x_4423_, 0, v___x_4425_);
                    v___x_4428_ = v___x_4423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4429_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4429_, 1, v___x_4426_);
                    v___x_4428_ = v_reuseFailAlloc_4429_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_4410_ = v___x_4428_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(
    mut v___y_4437_: *mut leanh::LeanObject,
    mut v_as_4438_: *mut leanh::LeanObject,
    mut v_i_4439_: *mut leanh::LeanObject,
    mut v_stop_4440_: *mut leanh::LeanObject,
    mut v_b_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4442_: usize = 0;
    let mut v_stop_boxed_4443_: usize = 0;
    let mut v_res_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4442_ = leanh::lean_unbox_usize(v_i_4439_);
    leanh::lean_dec(v_i_4439_);
    v_stop_boxed_4443_ = leanh::lean_unbox_usize(v_stop_4440_);
    leanh::lean_dec(v_stop_4440_);
    v_res_4444_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(
            v___y_4437_,
            v_as_4438_,
            v_i_boxed_4442_,
            v_stop_boxed_4443_,
            v_b_4441_,
        );
    leanh::lean_dec_ref(v_as_4438_);
    return v_res_4444_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__1___redArg(
    mut v_as_x27_4446_: *mut leanh::LeanObject,
    mut v_b_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: u8 = 0;
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_4446_) == 0 {
                    v___x_4449_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4449_, 0, v_b_4447_);
                    return v___x_4449_;
                } else {
                    v_head_4450_ = leanh::lean_ctor_get(v_as_x27_4446_, 0);
                    v_tail_4451_ = leanh::lean_ctor_get(v_as_x27_4446_, 1);
                    v_fst_4452_ = leanh::lean_ctor_get(v_b_4447_, 0);
                    v_snd_4453_ = leanh::lean_ctor_get(v_b_4447_, 1);
                    v_isSharedCheck_4478_ = (!leanh::lean_is_exclusive(v_b_4447_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4455_ = v_b_4447_;
                        v_isShared_4456_ = v_isSharedCheck_4478_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4453_);
                        leanh::lean_inc(v_fst_4452_);
                        leanh::lean_dec(v_b_4447_);
                        v___x_4455_ = leanh::lean_box(0);
                        v_isShared_4456_ = v_isSharedCheck_4478_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4457_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0;
                v___x_4458_ = lean_string_dec_eq(v_head_4450_, v___x_4457_);
                if v___x_4458_ == 0 {
                    leanh::lean_inc(v_head_4450_);
                    v___x_4459_ = l___private_LeanIR_0__setConfigOption(v_snd_4453_, v_head_4450_);
                    if leanh::lean_obj_tag(v___x_4459_) == 0 {
                        v_a_4460_ = leanh::lean_ctor_get(v___x_4459_, 0);
                        leanh::lean_inc(v_a_4460_);
                        leanh::lean_dec_ref_known(v___x_4459_, 1);
                        if v_isShared_4456_ == 0 {
                            leanh::lean_ctor_set(v___x_4455_, 1, v_a_4460_);
                            v___x_4462_ = v___x_4455_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4464_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_fst_4452_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_a_4460_);
                            v___x_4462_ = v_reuseFailAlloc_4464_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4455_);
                        leanh::lean_dec(v_fst_4452_);
                        v_a_4465_ = leanh::lean_ctor_get(v___x_4459_, 0);
                        v_isSharedCheck_4472_ =
                            (!leanh::lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4472_ == 0 {
                            v___x_4467_ = v___x_4459_;
                            v_isShared_4468_ = v_isSharedCheck_4472_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4465_);
                            leanh::lean_dec(v___x_4459_);
                            v___x_4467_ = leanh::lean_box(0);
                            v_isShared_4468_ = v_isSharedCheck_4472_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_4452_);
                    v___x_4473_ = leanh::lean_box((v___x_4458_) as usize);
                    if v_isShared_4456_ == 0 {
                        leanh::lean_ctor_set(v___x_4455_, 0, v___x_4473_);
                        v___x_4475_ = v___x_4455_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4477_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4473_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_snd_4453_);
                        v___x_4475_ = v_reuseFailAlloc_4477_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_as_x27_4446_ = v_tail_4451_;
                v_b_4447_ = v___x_4462_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4468_ == 0 {
                    v___x_4470_ = v___x_4467_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4470_;
            }
            5 => {
                v_as_x27_4446_ = v_tail_4451_;
                v_b_4447_ = v___x_4475_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(
    mut v_as_x27_4479_: *mut leanh::LeanObject,
    mut v_b_4480_: *mut leanh::LeanObject,
    mut v___y_4481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_4479_, v_b_4480_);
    leanh::lean_dec(v_as_x27_4479_);
    return v_res_4482_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(
    mut v_as_4483_: *mut leanh::LeanObject,
    mut v_i_4484_: usize,
    mut v_stop_4485_: usize,
    mut v_b_4486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4487_: u8 = 0;
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: usize = 0;
    let mut v___x_4495_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4487_ = lean_usize_dec_eq(v_i_4484_, v_stop_4485_);
                if v___x_4487_ == 0 {
                    v___x_4488_ = l_Lean_Compiler_LCNF_impureSigExt;
                    v_toEnvExtension_4489_ = leanh::lean_ctor_get(v___x_4488_, 0);
                    v_asyncMode_4490_ = leanh::lean_ctor_get(v_toEnvExtension_4489_, 2);
                    v___x_4491_ = leanh::lean_box(0);
                    v___x_4492_ = lean_array_uget_borrowed(v_as_4483_, v_i_4484_);
                    leanh::lean_inc(v___x_4492_);
                    v___x_4493_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                        v___x_4488_,
                        v_b_4486_,
                        v___x_4492_,
                        v_asyncMode_4490_,
                        v___x_4491_,
                    );
                    v___x_4494_ = 1usize;
                    v___x_4495_ = lean_usize_add(v_i_4484_, v___x_4494_);
                    v_i_4484_ = v___x_4495_;
                    v_b_4486_ = v___x_4493_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4486_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(
    mut v_as_4497_: *mut leanh::LeanObject,
    mut v_i_4498_: *mut leanh::LeanObject,
    mut v_stop_4499_: *mut leanh::LeanObject,
    mut v_b_4500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4501_: usize = 0;
    let mut v_stop_boxed_4502_: usize = 0;
    let mut v_res_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4501_ = leanh::lean_unbox_usize(v_i_4498_);
    leanh::lean_dec(v_i_4498_);
    v_stop_boxed_4502_ = leanh::lean_unbox_usize(v_stop_4499_);
    leanh::lean_dec(v_stop_4499_);
    v_res_4503_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(
            v_as_4497_,
            v_i_boxed_4501_,
            v_stop_boxed_4502_,
            v_b_4500_,
        );
    leanh::lean_dec_ref(v_as_4497_);
    return v_res_4503_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(
    mut v_as_4507_: *mut leanh::LeanObject,
    mut v_sz_4508_: usize,
    mut v_i_4509_: usize,
    mut v_b_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: u8 = 0;
    let mut v_a_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: usize = 0;
    let mut v___x_4521_: usize = 0;
    let mut v_a_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v_ref_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4513_ = lean_usize_dec_lt(v_i_4509_, v_sz_4508_);
                if v___x_4513_ == 0 {
                    v___x_4514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4514_, 0, v_b_4510_);
                    return v___x_4514_;
                } else {
                    leanh::lean_dec_ref(v_b_4510_);
                    v___x_4515_ = 0;
                    v_a_4516_ = lean_array_uget_borrowed(v_as_4507_, v_i_4509_);
                    leanh::lean_inc(v_a_4516_);
                    v___x_4517_ = l_Lean_Message_toString(v_a_4516_, v___x_4515_);
                    v___x_4518_ = l_IO_eprintln___at___00main_spec__6(v___x_4517_);
                    if leanh::lean_obj_tag(v___x_4518_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4518_, 1);
                        v___x_4519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0;
                        v___x_4520_ = 1usize;
                        v___x_4521_ = lean_usize_add(v_i_4509_, v___x_4520_);
                        v_i_4509_ = v___x_4521_;
                        v_b_4510_ = v___x_4519_;
                        state = 0;
                        continue;
                    } else {
                        v_a_4523_ = leanh::lean_ctor_get(v___x_4518_, 0);
                        v_isSharedCheck_4535_ =
                            (!leanh::lean_is_exclusive(v___x_4518_)) as u8;
                        if v_isSharedCheck_4535_ == 0 {
                            v___x_4525_ = v___x_4518_;
                            v_isShared_4526_ = v_isSharedCheck_4535_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4523_);
                            leanh::lean_dec(v___x_4518_);
                            v___x_4525_ = leanh::lean_box(0);
                            v_isShared_4526_ = v_isSharedCheck_4535_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_ref_4527_ = leanh::lean_ctor_get(v___y_4511_, 5);
                v___x_4528_ = lean_io_error_to_string(v_a_4523_);
                v___x_4529_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4529_, 0, v___x_4528_);
                v___x_4530_ = l_Lean_MessageData_ofFormat(v___x_4529_);
                leanh::lean_inc(v_ref_4527_);
                v___x_4531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4531_, 0, v_ref_4527_);
                leanh::lean_ctor_set(v___x_4531_, 1, v___x_4530_);
                if v_isShared_4526_ == 0 {
                    leanh::lean_ctor_set(v___x_4525_, 0, v___x_4531_);
                    v___x_4533_ = v___x_4525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4534_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v___x_4531_);
                    v___x_4533_ = v_reuseFailAlloc_4534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(
    mut v_as_4536_: *mut leanh::LeanObject,
    mut v_sz_4537_: *mut leanh::LeanObject,
    mut v_i_4538_: *mut leanh::LeanObject,
    mut v_b_4539_: *mut leanh::LeanObject,
    mut v___y_4540_: *mut leanh::LeanObject,
    mut v___y_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4542_: usize = 0;
    let mut v_i_boxed_4543_: usize = 0;
    let mut v_res_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4542_ = leanh::lean_unbox_usize(v_sz_4537_);
    leanh::lean_dec(v_sz_4537_);
    v_i_boxed_4543_ = leanh::lean_unbox_usize(v_i_4538_);
    leanh::lean_dec(v_i_4538_);
    v_res_4544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_4536_, v_sz_boxed_4542_, v_i_boxed_4543_, v_b_4539_, v___y_4540_);
    leanh::lean_dec_ref(v___y_4540_);
    leanh::lean_dec_ref(v_as_4536_);
    return v_res_4544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(
    mut v_as_4545_: *mut leanh::LeanObject,
    mut v_sz_4546_: usize,
    mut v_i_4547_: usize,
    mut v_b_4548_: *mut leanh::LeanObject,
    mut v___y_4549_: *mut leanh::LeanObject,
    mut v___y_4550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4552_: u8 = 0;
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: u8 = 0;
    let mut v_a_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: usize = 0;
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v_ref_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4552_ = lean_usize_dec_lt(v_i_4547_, v_sz_4546_);
                if v___x_4552_ == 0 {
                    v___x_4553_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4553_, 0, v_b_4548_);
                    return v___x_4553_;
                } else {
                    leanh::lean_dec_ref(v_b_4548_);
                    v___x_4554_ = 0;
                    v_a_4555_ = lean_array_uget_borrowed(v_as_4545_, v_i_4547_);
                    leanh::lean_inc(v_a_4555_);
                    v___x_4556_ = l_Lean_Message_toString(v_a_4555_, v___x_4554_);
                    v___x_4557_ = l_IO_eprintln___at___00main_spec__6(v___x_4556_);
                    if leanh::lean_obj_tag(v___x_4557_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4557_, 1);
                        v___x_4558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0;
                        v___x_4559_ = 1usize;
                        v___x_4560_ = lean_usize_add(v_i_4547_, v___x_4559_);
                        v___x_4561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_4545_, v_sz_4546_, v___x_4560_, v___x_4558_, v___y_4549_);
                        return v___x_4561_;
                    } else {
                        v_a_4562_ = leanh::lean_ctor_get(v___x_4557_, 0);
                        v_isSharedCheck_4574_ =
                            (!leanh::lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4574_ == 0 {
                            v___x_4564_ = v___x_4557_;
                            v_isShared_4565_ = v_isSharedCheck_4574_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4562_);
                            leanh::lean_dec(v___x_4557_);
                            v___x_4564_ = leanh::lean_box(0);
                            v_isShared_4565_ = v_isSharedCheck_4574_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_ref_4566_ = leanh::lean_ctor_get(v___y_4549_, 5);
                v___x_4567_ = lean_io_error_to_string(v_a_4562_);
                v___x_4568_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4568_, 0, v___x_4567_);
                v___x_4569_ = l_Lean_MessageData_ofFormat(v___x_4568_);
                leanh::lean_inc(v_ref_4566_);
                v___x_4570_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4570_, 0, v_ref_4566_);
                leanh::lean_ctor_set(v___x_4570_, 1, v___x_4569_);
                if v_isShared_4565_ == 0 {
                    leanh::lean_ctor_set(v___x_4564_, 0, v___x_4570_);
                    v___x_4572_ = v___x_4564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
                    v___x_4572_ = v_reuseFailAlloc_4573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(
    mut v_as_4575_: *mut leanh::LeanObject,
    mut v_sz_4576_: *mut leanh::LeanObject,
    mut v_i_4577_: *mut leanh::LeanObject,
    mut v_b_4578_: *mut leanh::LeanObject,
    mut v___y_4579_: *mut leanh::LeanObject,
    mut v___y_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4582_: usize = 0;
    let mut v_i_boxed_4583_: usize = 0;
    let mut v_res_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4582_ = leanh::lean_unbox_usize(v_sz_4576_);
    leanh::lean_dec(v_sz_4576_);
    v_i_boxed_4583_ = leanh::lean_unbox_usize(v_i_4577_);
    leanh::lean_dec(v_i_4577_);
    v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_4575_, v_sz_boxed_4582_, v_i_boxed_4583_, v_b_4578_, v___y_4579_, v___y_4580_);
    leanh::lean_dec(v___y_4580_);
    leanh::lean_dec_ref(v___y_4579_);
    leanh::lean_dec_ref(v_as_4575_);
    return v_res_4584_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(
    mut v_as_4588_: *mut leanh::LeanObject,
    mut v_sz_4589_: usize,
    mut v_i_4590_: usize,
    mut v_b_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4594_: u8 = 0;
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: u8 = 0;
    let mut v_a_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: usize = 0;
    let mut v___x_4602_: usize = 0;
    let mut v_a_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4607_: u8 = 0;
    let mut v_ref_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4594_ = lean_usize_dec_lt(v_i_4590_, v_sz_4589_);
                if v___x_4594_ == 0 {
                    v___x_4595_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4595_, 0, v_b_4591_);
                    return v___x_4595_;
                } else {
                    leanh::lean_dec_ref(v_b_4591_);
                    v___x_4596_ = 0;
                    v_a_4597_ = lean_array_uget_borrowed(v_as_4588_, v_i_4590_);
                    leanh::lean_inc(v_a_4597_);
                    v___x_4598_ = l_Lean_Message_toString(v_a_4597_, v___x_4596_);
                    v___x_4599_ = l_IO_eprintln___at___00main_spec__6(v___x_4598_);
                    if leanh::lean_obj_tag(v___x_4599_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4599_, 1);
                        v___x_4600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0;
                        v___x_4601_ = 1usize;
                        v___x_4602_ = lean_usize_add(v_i_4590_, v___x_4601_);
                        v_i_4590_ = v___x_4602_;
                        v_b_4591_ = v___x_4600_;
                        state = 0;
                        continue;
                    } else {
                        v_a_4604_ = leanh::lean_ctor_get(v___x_4599_, 0);
                        v_isSharedCheck_4616_ =
                            (!leanh::lean_is_exclusive(v___x_4599_)) as u8;
                        if v_isSharedCheck_4616_ == 0 {
                            v___x_4606_ = v___x_4599_;
                            v_isShared_4607_ = v_isSharedCheck_4616_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4604_);
                            leanh::lean_dec(v___x_4599_);
                            v___x_4606_ = leanh::lean_box(0);
                            v_isShared_4607_ = v_isSharedCheck_4616_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_ref_4608_ = leanh::lean_ctor_get(v___y_4592_, 5);
                v___x_4609_ = lean_io_error_to_string(v_a_4604_);
                v___x_4610_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4610_, 0, v___x_4609_);
                v___x_4611_ = l_Lean_MessageData_ofFormat(v___x_4610_);
                leanh::lean_inc(v_ref_4608_);
                v___x_4612_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4612_, 0, v_ref_4608_);
                leanh::lean_ctor_set(v___x_4612_, 1, v___x_4611_);
                if v_isShared_4607_ == 0 {
                    leanh::lean_ctor_set(v___x_4606_, 0, v___x_4612_);
                    v___x_4614_ = v___x_4606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4615_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
                    v___x_4614_ = v_reuseFailAlloc_4615_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(
    mut v_as_4617_: *mut leanh::LeanObject,
    mut v_sz_4618_: *mut leanh::LeanObject,
    mut v_i_4619_: *mut leanh::LeanObject,
    mut v_b_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
    mut v___y_4622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4623_: usize = 0;
    let mut v_i_boxed_4624_: usize = 0;
    let mut v_res_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4623_ = leanh::lean_unbox_usize(v_sz_4618_);
    leanh::lean_dec(v_sz_4618_);
    v_i_boxed_4624_ = leanh::lean_unbox_usize(v_i_4619_);
    leanh::lean_dec(v_i_4619_);
    v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_4617_, v_sz_boxed_4623_, v_i_boxed_4624_, v_b_4620_, v___y_4621_);
    leanh::lean_dec_ref(v___y_4621_);
    leanh::lean_dec_ref(v_as_4617_);
    return v_res_4625_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(
    mut v_as_4626_: *mut leanh::LeanObject,
    mut v_sz_4627_: usize,
    mut v_i_4628_: usize,
    mut v_b_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4633_: u8 = 0;
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: u8 = 0;
    let mut v_a_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: usize = 0;
    let mut v___x_4641_: usize = 0;
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v_ref_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4633_ = lean_usize_dec_lt(v_i_4628_, v_sz_4627_);
                if v___x_4633_ == 0 {
                    v___x_4634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4634_, 0, v_b_4629_);
                    return v___x_4634_;
                } else {
                    leanh::lean_dec_ref(v_b_4629_);
                    v___x_4635_ = 0;
                    v_a_4636_ = lean_array_uget_borrowed(v_as_4626_, v_i_4628_);
                    leanh::lean_inc(v_a_4636_);
                    v___x_4637_ = l_Lean_Message_toString(v_a_4636_, v___x_4635_);
                    v___x_4638_ = l_IO_eprintln___at___00main_spec__6(v___x_4637_);
                    if leanh::lean_obj_tag(v___x_4638_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4638_, 1);
                        v___x_4639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0;
                        v___x_4640_ = 1usize;
                        v___x_4641_ = lean_usize_add(v_i_4628_, v___x_4640_);
                        v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_4626_, v_sz_4627_, v___x_4641_, v___x_4639_, v___y_4630_);
                        return v___x_4642_;
                    } else {
                        v_a_4643_ = leanh::lean_ctor_get(v___x_4638_, 0);
                        v_isSharedCheck_4655_ =
                            (!leanh::lean_is_exclusive(v___x_4638_)) as u8;
                        if v_isSharedCheck_4655_ == 0 {
                            v___x_4645_ = v___x_4638_;
                            v_isShared_4646_ = v_isSharedCheck_4655_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4643_);
                            leanh::lean_dec(v___x_4638_);
                            v___x_4645_ = leanh::lean_box(0);
                            v_isShared_4646_ = v_isSharedCheck_4655_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_ref_4647_ = leanh::lean_ctor_get(v___y_4630_, 5);
                v___x_4648_ = lean_io_error_to_string(v_a_4643_);
                v___x_4649_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4649_, 0, v___x_4648_);
                v___x_4650_ = l_Lean_MessageData_ofFormat(v___x_4649_);
                leanh::lean_inc(v_ref_4647_);
                v___x_4651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4651_, 0, v_ref_4647_);
                leanh::lean_ctor_set(v___x_4651_, 1, v___x_4650_);
                if v_isShared_4646_ == 0 {
                    leanh::lean_ctor_set(v___x_4645_, 0, v___x_4651_);
                    v___x_4653_ = v___x_4645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4654_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4651_);
                    v___x_4653_ = v_reuseFailAlloc_4654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(
    mut v_as_4656_: *mut leanh::LeanObject,
    mut v_sz_4657_: *mut leanh::LeanObject,
    mut v_i_4658_: *mut leanh::LeanObject,
    mut v_b_4659_: *mut leanh::LeanObject,
    mut v___y_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
    mut v___y_4662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4663_: usize = 0;
    let mut v_i_boxed_4664_: usize = 0;
    let mut v_res_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4663_ = leanh::lean_unbox_usize(v_sz_4657_);
    leanh::lean_dec(v_sz_4657_);
    v_i_boxed_4664_ = leanh::lean_unbox_usize(v_i_4658_);
    leanh::lean_dec(v_i_4658_);
    v_res_4665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_4656_, v_sz_boxed_4663_, v_i_boxed_4664_, v_b_4659_, v___y_4660_, v___y_4661_);
    leanh::lean_dec(v___y_4661_);
    leanh::lean_dec_ref(v___y_4660_);
    leanh::lean_dec_ref(v_as_4656_);
    return v_res_4665_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(
    mut v_init_4666_: *mut leanh::LeanObject,
    mut v_n_4667_: *mut leanh::LeanObject,
    mut v_b_4668_: *mut leanh::LeanObject,
    mut v___y_4669_: *mut leanh::LeanObject,
    mut v___y_4670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4675_: usize = 0;
    let mut v___x_4676_: usize = 0;
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v_fst_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_a_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4696_: u8 = 0;
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut v_vs_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4704_: usize = 0;
    let mut v___x_4705_: usize = 0;
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4710_: u8 = 0;
    let mut v_fst_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4721_: u8 = 0;
    let mut v_a_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_4667_) == 0 {
                    v_cs_4672_ = leanh::lean_ctor_get(v_n_4667_, 0);
                    v___x_4673_ = leanh::lean_box(0);
                    v___x_4674_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4674_, 0, v___x_4673_);
                    leanh::lean_ctor_set(v___x_4674_, 1, v_b_4668_);
                    v_sz_4675_ = lean_array_size(v_cs_4672_);
                    v___x_4676_ = 0usize;
                    v___x_4677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_4666_, v_cs_4672_, v_sz_4675_, v___x_4676_, v___x_4674_, v___y_4669_, v___y_4670_);
                    if leanh::lean_obj_tag(v___x_4677_) == 0 {
                        v_a_4678_ = leanh::lean_ctor_get(v___x_4677_, 0);
                        v_isSharedCheck_4692_ =
                            (!leanh::lean_is_exclusive(v___x_4677_)) as u8;
                        if v_isSharedCheck_4692_ == 0 {
                            v___x_4680_ = v___x_4677_;
                            v_isShared_4681_ = v_isSharedCheck_4692_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4678_);
                            leanh::lean_dec(v___x_4677_);
                            v___x_4680_ = leanh::lean_box(0);
                            v_isShared_4681_ = v_isSharedCheck_4692_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4693_ = leanh::lean_ctor_get(v___x_4677_, 0);
                        v_isSharedCheck_4700_ =
                            (!leanh::lean_is_exclusive(v___x_4677_)) as u8;
                        if v_isSharedCheck_4700_ == 0 {
                            v___x_4695_ = v___x_4677_;
                            v_isShared_4696_ = v_isSharedCheck_4700_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4693_);
                            leanh::lean_dec(v___x_4677_);
                            v___x_4695_ = leanh::lean_box(0);
                            v_isShared_4696_ = v_isSharedCheck_4700_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4701_ = leanh::lean_ctor_get(v_n_4667_, 0);
                    v___x_4702_ = leanh::lean_box(0);
                    v___x_4703_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4703_, 0, v___x_4702_);
                    leanh::lean_ctor_set(v___x_4703_, 1, v_b_4668_);
                    v_sz_4704_ = lean_array_size(v_vs_4701_);
                    v___x_4705_ = 0usize;
                    v___x_4706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_4701_, v_sz_4704_, v___x_4705_, v___x_4703_, v___y_4669_, v___y_4670_);
                    if leanh::lean_obj_tag(v___x_4706_) == 0 {
                        v_a_4707_ = leanh::lean_ctor_get(v___x_4706_, 0);
                        v_isSharedCheck_4721_ =
                            (!leanh::lean_is_exclusive(v___x_4706_)) as u8;
                        if v_isSharedCheck_4721_ == 0 {
                            v___x_4709_ = v___x_4706_;
                            v_isShared_4710_ = v_isSharedCheck_4721_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4707_);
                            leanh::lean_dec(v___x_4706_);
                            v___x_4709_ = leanh::lean_box(0);
                            v_isShared_4710_ = v_isSharedCheck_4721_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4722_ = leanh::lean_ctor_get(v___x_4706_, 0);
                        v_isSharedCheck_4729_ =
                            (!leanh::lean_is_exclusive(v___x_4706_)) as u8;
                        if v_isSharedCheck_4729_ == 0 {
                            v___x_4724_ = v___x_4706_;
                            v_isShared_4725_ = v_isSharedCheck_4729_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4722_);
                            leanh::lean_dec(v___x_4706_);
                            v___x_4724_ = leanh::lean_box(0);
                            v_isShared_4725_ = v_isSharedCheck_4729_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4682_ = leanh::lean_ctor_get(v_a_4678_, 0);
                if leanh::lean_obj_tag(v_fst_4682_) == 0 {
                    v_snd_4683_ = leanh::lean_ctor_get(v_a_4678_, 1);
                    leanh::lean_inc(v_snd_4683_);
                    leanh::lean_dec(v_a_4678_);
                    v___x_4684_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4684_, 0, v_snd_4683_);
                    if v_isShared_4681_ == 0 {
                        leanh::lean_ctor_set(v___x_4680_, 0, v___x_4684_);
                        v___x_4686_ = v___x_4680_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4687_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4684_);
                        v___x_4686_ = v_reuseFailAlloc_4687_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4682_);
                    leanh::lean_dec(v_a_4678_);
                    v_val_4688_ = leanh::lean_ctor_get(v_fst_4682_, 0);
                    leanh::lean_inc(v_val_4688_);
                    leanh::lean_dec_ref_known(v_fst_4682_, 1);
                    if v_isShared_4681_ == 0 {
                        leanh::lean_ctor_set(v___x_4680_, 0, v_val_4688_);
                        v___x_4690_ = v___x_4680_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_val_4688_);
                        v___x_4690_ = v_reuseFailAlloc_4691_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4686_;
            }
            3 => {
                return v___x_4690_;
            }
            4 => {
                if v_isShared_4696_ == 0 {
                    v___x_4698_ = v___x_4695_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
                    v___x_4698_ = v_reuseFailAlloc_4699_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4698_;
            }
            6 => {
                v_fst_4711_ = leanh::lean_ctor_get(v_a_4707_, 0);
                if leanh::lean_obj_tag(v_fst_4711_) == 0 {
                    v_snd_4712_ = leanh::lean_ctor_get(v_a_4707_, 1);
                    leanh::lean_inc(v_snd_4712_);
                    leanh::lean_dec(v_a_4707_);
                    v___x_4713_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4713_, 0, v_snd_4712_);
                    if v_isShared_4710_ == 0 {
                        leanh::lean_ctor_set(v___x_4709_, 0, v___x_4713_);
                        v___x_4715_ = v___x_4709_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4713_);
                        v___x_4715_ = v_reuseFailAlloc_4716_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4711_);
                    leanh::lean_dec(v_a_4707_);
                    v_val_4717_ = leanh::lean_ctor_get(v_fst_4711_, 0);
                    leanh::lean_inc(v_val_4717_);
                    leanh::lean_dec_ref_known(v_fst_4711_, 1);
                    if v_isShared_4710_ == 0 {
                        leanh::lean_ctor_set(v___x_4709_, 0, v_val_4717_);
                        v___x_4719_ = v___x_4709_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_val_4717_);
                        v___x_4719_ = v_reuseFailAlloc_4720_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4715_;
            }
            8 => {
                return v___x_4719_;
            }
            9 => {
                if v_isShared_4725_ == 0 {
                    v___x_4727_ = v___x_4724_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
                    v___x_4727_ = v_reuseFailAlloc_4728_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(
    mut v_init_4730_: *mut leanh::LeanObject,
    mut v_as_4731_: *mut leanh::LeanObject,
    mut v_sz_4732_: usize,
    mut v_i_4733_: usize,
    mut v_b_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4738_: u8 = 0;
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4743_: u8 = 0;
    let mut v_a_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: usize = 0;
    let mut v___x_4762_: usize = 0;
    let mut v_reuseFailAlloc_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4765_: u8 = 0;
    let mut v_a_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_unused_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4738_ = lean_usize_dec_lt(v_i_4733_, v_sz_4732_);
                if v___x_4738_ == 0 {
                    v___x_4739_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4739_, 0, v_b_4734_);
                    return v___x_4739_;
                } else {
                    v_snd_4740_ = leanh::lean_ctor_get(v_b_4734_, 1);
                    v_isSharedCheck_4774_ = (!leanh::lean_is_exclusive(v_b_4734_)) as u8;
                    if v_isSharedCheck_4774_ == 0 {
                        v_unused_4775_ = leanh::lean_ctor_get(v_b_4734_, 0);
                        leanh::lean_dec(v_unused_4775_);
                        v___x_4742_ = v_b_4734_;
                        v_isShared_4743_ = v_isSharedCheck_4774_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4740_);
                        leanh::lean_dec(v_b_4734_);
                        v___x_4742_ = leanh::lean_box(0);
                        v_isShared_4743_ = v_isSharedCheck_4774_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4744_ = lean_array_uget_borrowed(v_as_4731_, v_i_4733_);
                leanh::lean_inc(v_snd_4740_);
                v___x_4745_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_4730_, v_a_4744_, v_snd_4740_, v___y_4735_, v___y_4736_);
                if leanh::lean_obj_tag(v___x_4745_) == 0 {
                    v_a_4746_ = leanh::lean_ctor_get(v___x_4745_, 0);
                    v_isSharedCheck_4765_ = (!leanh::lean_is_exclusive(v___x_4745_)) as u8;
                    if v_isSharedCheck_4765_ == 0 {
                        v___x_4748_ = v___x_4745_;
                        v_isShared_4749_ = v_isSharedCheck_4765_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4746_);
                        leanh::lean_dec(v___x_4745_);
                        v___x_4748_ = leanh::lean_box(0);
                        v_isShared_4749_ = v_isSharedCheck_4765_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4742_);
                    leanh::lean_dec(v_snd_4740_);
                    v_a_4766_ = leanh::lean_ctor_get(v___x_4745_, 0);
                    v_isSharedCheck_4773_ = (!leanh::lean_is_exclusive(v___x_4745_)) as u8;
                    if v_isSharedCheck_4773_ == 0 {
                        v___x_4768_ = v___x_4745_;
                        v_isShared_4769_ = v_isSharedCheck_4773_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4766_);
                        leanh::lean_dec(v___x_4745_);
                        v___x_4768_ = leanh::lean_box(0);
                        v_isShared_4769_ = v_isSharedCheck_4773_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4746_) == 0 {
                    v___x_4750_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4750_, 0, v_a_4746_);
                    if v_isShared_4743_ == 0 {
                        leanh::lean_ctor_set(v___x_4742_, 0, v___x_4750_);
                        v___x_4752_ = v___x_4742_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4750_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_snd_4740_);
                        v___x_4752_ = v_reuseFailAlloc_4756_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4748_);
                    leanh::lean_dec(v_snd_4740_);
                    v_a_4757_ = leanh::lean_ctor_get(v_a_4746_, 0);
                    leanh::lean_inc(v_a_4757_);
                    leanh::lean_dec_ref_known(v_a_4746_, 1);
                    v___x_4758_ = leanh::lean_box(0);
                    if v_isShared_4743_ == 0 {
                        leanh::lean_ctor_set(v___x_4742_, 1, v_a_4757_);
                        leanh::lean_ctor_set(v___x_4742_, 0, v___x_4758_);
                        v___x_4760_ = v___x_4742_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4764_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4758_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_a_4757_);
                        v___x_4760_ = v_reuseFailAlloc_4764_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4749_ == 0 {
                    leanh::lean_ctor_set(v___x_4748_, 0, v___x_4752_);
                    v___x_4754_ = v___x_4748_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4755_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4752_);
                    v___x_4754_ = v_reuseFailAlloc_4755_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4754_;
            }
            5 => {
                v___x_4761_ = 1usize;
                v___x_4762_ = lean_usize_add(v_i_4733_, v___x_4761_);
                v_i_4733_ = v___x_4762_;
                v_b_4734_ = v___x_4760_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4769_ == 0 {
                    v___x_4771_ = v___x_4768_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4772_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4772_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(
    mut v_init_4776_: *mut leanh::LeanObject,
    mut v_as_4777_: *mut leanh::LeanObject,
    mut v_sz_4778_: *mut leanh::LeanObject,
    mut v_i_4779_: *mut leanh::LeanObject,
    mut v_b_4780_: *mut leanh::LeanObject,
    mut v___y_4781_: *mut leanh::LeanObject,
    mut v___y_4782_: *mut leanh::LeanObject,
    mut v___y_4783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4784_: usize = 0;
    let mut v_i_boxed_4785_: usize = 0;
    let mut v_res_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4784_ = leanh::lean_unbox_usize(v_sz_4778_);
    leanh::lean_dec(v_sz_4778_);
    v_i_boxed_4785_ = leanh::lean_unbox_usize(v_i_4779_);
    leanh::lean_dec(v_i_4779_);
    v_res_4786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_4776_, v_as_4777_, v_sz_boxed_4784_, v_i_boxed_4785_, v_b_4780_, v___y_4781_, v___y_4782_);
    leanh::lean_dec(v___y_4782_);
    leanh::lean_dec_ref(v___y_4781_);
    leanh::lean_dec_ref(v_as_4777_);
    return v_res_4786_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(
    mut v_init_4787_: *mut leanh::LeanObject,
    mut v_n_4788_: *mut leanh::LeanObject,
    mut v_b_4789_: *mut leanh::LeanObject,
    mut v___y_4790_: *mut leanh::LeanObject,
    mut v___y_4791_: *mut leanh::LeanObject,
    mut v___y_4792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4793_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_4787_, v_n_4788_, v_b_4789_, v___y_4790_, v___y_4791_);
    leanh::lean_dec(v___y_4791_);
    leanh::lean_dec_ref(v___y_4790_);
    leanh::lean_dec_ref(v_n_4788_);
    return v_res_4793_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00main_spec__12(
    mut v_t_4794_: *mut leanh::LeanObject,
    mut v_init_4795_: *mut leanh::LeanObject,
    mut v___y_4796_: *mut leanh::LeanObject,
    mut v___y_4797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v_a_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4813_: usize = 0;
    let mut v___x_4814_: usize = 0;
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v_fst_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4829_: u8 = 0;
    let mut v_a_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4833_: u8 = 0;
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4837_: u8 = 0;
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_a_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4799_ = leanh::lean_ctor_get(v_t_4794_, 0);
                v_tail_4800_ = leanh::lean_ctor_get(v_t_4794_, 1);
                v___x_4801_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_4795_, v_root_4799_, v_init_4795_, v___y_4796_, v___y_4797_);
                if leanh::lean_obj_tag(v___x_4801_) == 0 {
                    v_a_4802_ = leanh::lean_ctor_get(v___x_4801_, 0);
                    v_isSharedCheck_4838_ = (!leanh::lean_is_exclusive(v___x_4801_)) as u8;
                    if v_isSharedCheck_4838_ == 0 {
                        v___x_4804_ = v___x_4801_;
                        v_isShared_4805_ = v_isSharedCheck_4838_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4802_);
                        leanh::lean_dec(v___x_4801_);
                        v___x_4804_ = leanh::lean_box(0);
                        v_isShared_4805_ = v_isSharedCheck_4838_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4839_ = leanh::lean_ctor_get(v___x_4801_, 0);
                    v_isSharedCheck_4846_ = (!leanh::lean_is_exclusive(v___x_4801_)) as u8;
                    if v_isSharedCheck_4846_ == 0 {
                        v___x_4841_ = v___x_4801_;
                        v_isShared_4842_ = v_isSharedCheck_4846_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4839_);
                        leanh::lean_dec(v___x_4801_);
                        v___x_4841_ = leanh::lean_box(0);
                        v_isShared_4842_ = v_isSharedCheck_4846_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4802_) == 0 {
                    v_a_4806_ = leanh::lean_ctor_get(v_a_4802_, 0);
                    leanh::lean_inc(v_a_4806_);
                    leanh::lean_dec_ref_known(v_a_4802_, 1);
                    if v_isShared_4805_ == 0 {
                        leanh::lean_ctor_set(v___x_4804_, 0, v_a_4806_);
                        v___x_4808_ = v___x_4804_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4809_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4806_);
                        v___x_4808_ = v_reuseFailAlloc_4809_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4804_);
                    v_a_4810_ = leanh::lean_ctor_get(v_a_4802_, 0);
                    leanh::lean_inc(v_a_4810_);
                    leanh::lean_dec_ref_known(v_a_4802_, 1);
                    v___x_4811_ = leanh::lean_box(0);
                    v___x_4812_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4812_, 0, v___x_4811_);
                    leanh::lean_ctor_set(v___x_4812_, 1, v_a_4810_);
                    v_sz_4813_ = lean_array_size(v_tail_4800_);
                    v___x_4814_ = 0usize;
                    v___x_4815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_4800_, v_sz_4813_, v___x_4814_, v___x_4812_, v___y_4796_, v___y_4797_);
                    if leanh::lean_obj_tag(v___x_4815_) == 0 {
                        v_a_4816_ = leanh::lean_ctor_get(v___x_4815_, 0);
                        v_isSharedCheck_4829_ =
                            (!leanh::lean_is_exclusive(v___x_4815_)) as u8;
                        if v_isSharedCheck_4829_ == 0 {
                            v___x_4818_ = v___x_4815_;
                            v_isShared_4819_ = v_isSharedCheck_4829_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4816_);
                            leanh::lean_dec(v___x_4815_);
                            v___x_4818_ = leanh::lean_box(0);
                            v_isShared_4819_ = v_isSharedCheck_4829_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4830_ = leanh::lean_ctor_get(v___x_4815_, 0);
                        v_isSharedCheck_4837_ =
                            (!leanh::lean_is_exclusive(v___x_4815_)) as u8;
                        if v_isSharedCheck_4837_ == 0 {
                            v___x_4832_ = v___x_4815_;
                            v_isShared_4833_ = v_isSharedCheck_4837_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4830_);
                            leanh::lean_dec(v___x_4815_);
                            v___x_4832_ = leanh::lean_box(0);
                            v_isShared_4833_ = v_isSharedCheck_4837_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4808_;
            }
            3 => {
                v_fst_4820_ = leanh::lean_ctor_get(v_a_4816_, 0);
                if leanh::lean_obj_tag(v_fst_4820_) == 0 {
                    v_snd_4821_ = leanh::lean_ctor_get(v_a_4816_, 1);
                    leanh::lean_inc(v_snd_4821_);
                    leanh::lean_dec(v_a_4816_);
                    if v_isShared_4819_ == 0 {
                        leanh::lean_ctor_set(v___x_4818_, 0, v_snd_4821_);
                        v___x_4823_ = v___x_4818_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4824_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_snd_4821_);
                        v___x_4823_ = v_reuseFailAlloc_4824_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4820_);
                    leanh::lean_dec(v_a_4816_);
                    v_val_4825_ = leanh::lean_ctor_get(v_fst_4820_, 0);
                    leanh::lean_inc(v_val_4825_);
                    leanh::lean_dec_ref_known(v_fst_4820_, 1);
                    if v_isShared_4819_ == 0 {
                        leanh::lean_ctor_set(v___x_4818_, 0, v_val_4825_);
                        v___x_4827_ = v___x_4818_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_val_4825_);
                        v___x_4827_ = v_reuseFailAlloc_4828_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4823_;
            }
            5 => {
                return v___x_4827_;
            }
            6 => {
                if v_isShared_4833_ == 0 {
                    v___x_4835_ = v___x_4832_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4836_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
                    v___x_4835_ = v_reuseFailAlloc_4836_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4835_;
            }
            8 => {
                if v_isShared_4842_ == 0 {
                    v___x_4844_ = v___x_4841_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
                    v___x_4844_ = v_reuseFailAlloc_4845_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(
    mut v_t_4847_: *mut leanh::LeanObject,
    mut v_init_4848_: *mut leanh::LeanObject,
    mut v___y_4849_: *mut leanh::LeanObject,
    mut v___y_4850_: *mut leanh::LeanObject,
    mut v___y_4851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4852_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(
        v_t_4847_,
        v_init_4848_,
        v___y_4849_,
        v___y_4850_,
    );
    leanh::lean_dec(v___y_4850_);
    leanh::lean_dec_ref(v___y_4849_);
    leanh::lean_dec_ref(v_t_4847_);
    return v_res_4852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(
    mut v___x_4860_: u8,
    mut v_suppressElabErrors_4861_: u8,
    mut v___x_4862_: *mut leanh::LeanObject,
    mut v_x_4863_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4863_) == 1 {
        let mut v_pre_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_4864_ = leanh::lean_ctor_get(v_x_4863_, 0);
        match leanh::lean_obj_tag(v_pre_4864_) {
            1 => {
                let mut v_pre_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_4865_ = leanh::lean_ctor_get(v_pre_4864_, 0);
                match leanh::lean_obj_tag(v_pre_4865_) {
                    0 => {
                        let mut v_str_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4869_: u8 = 0;
                        v_str_4866_ = leanh::lean_ctor_get(v_x_4863_, 1);
                        v_str_4867_ = leanh::lean_ctor_get(v_pre_4864_, 1);
                        v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0;
                        v___x_4869_ = lean_string_dec_eq(v_str_4867_, v___x_4868_);
                        if v___x_4869_ == 0 {
                            let mut v___x_4870_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4871_: u8 = 0;
                            v___x_4870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1;
                            v___x_4871_ = lean_string_dec_eq(v_str_4867_, v___x_4870_);
                            if v___x_4871_ == 0 {
                                return v___x_4860_;
                            } else {
                                let mut v___x_4872_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4873_: u8 = 0;
                                v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2;
                                v___x_4873_ = lean_string_dec_eq(v_str_4866_, v___x_4872_);
                                if v___x_4873_ == 0 {
                                    return v___x_4860_;
                                } else {
                                    return v_suppressElabErrors_4861_;
                                }
                            }
                        } else {
                            let mut v___x_4874_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4875_: u8 = 0;
                            v___x_4874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3;
                            v___x_4875_ = lean_string_dec_eq(v_str_4866_, v___x_4874_);
                            if v___x_4875_ == 0 {
                                return v___x_4860_;
                            } else {
                                return v_suppressElabErrors_4861_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4876_ = leanh::lean_ctor_get(v_pre_4865_, 0);
                        if leanh::lean_obj_tag(v_pre_4876_) == 0 {
                            let mut v_str_4877_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4878_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4879_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4880_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4881_: u8 = 0;
                            v_str_4877_ = leanh::lean_ctor_get(v_x_4863_, 1);
                            v_str_4878_ = leanh::lean_ctor_get(v_pre_4864_, 1);
                            v_str_4879_ = leanh::lean_ctor_get(v_pre_4865_, 1);
                            v___x_4880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4;
                            v___x_4881_ = lean_string_dec_eq(v_str_4879_, v___x_4880_);
                            if v___x_4881_ == 0 {
                                return v___x_4860_;
                            } else {
                                let mut v___x_4882_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4883_: u8 = 0;
                                v___x_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5;
                                v___x_4883_ = lean_string_dec_eq(v_str_4878_, v___x_4882_);
                                if v___x_4883_ == 0 {
                                    return v___x_4860_;
                                } else {
                                    let mut v___x_4884_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4885_: u8 = 0;
                                    v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6;
                                    v___x_4885_ = lean_string_dec_eq(v_str_4877_, v___x_4884_);
                                    if v___x_4885_ == 0 {
                                        return v___x_4860_;
                                    } else {
                                        return v_suppressElabErrors_4861_;
                                    }
                                }
                            }
                        } else {
                            return v___x_4860_;
                        }
                    }
                    _ => {
                        return v___x_4860_;
                    }
                }
            }
            0 => {
                let mut v_str_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4887_: u8 = 0;
                v_str_4886_ = leanh::lean_ctor_get(v_x_4863_, 1);
                v___x_4887_ = lean_string_dec_eq(v_str_4886_, v___x_4862_);
                if v___x_4887_ == 0 {
                    return v___x_4860_;
                } else {
                    return v_suppressElabErrors_4861_;
                }
            }
            _ => {
                return v___x_4860_;
            }
        }
    } else {
        return v___x_4860_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(
    mut v___x_4888_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_4889_: *mut leanh::LeanObject,
    mut v___x_4890_: *mut leanh::LeanObject,
    mut v_x_4891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37203__boxed_4892_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4893_: u8 = 0;
    let mut v_res_4894_: u8 = 0;
    let mut v_r_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37203__boxed_4892_ = (leanh::lean_unbox(v___x_4888_) as u8);
    v_suppressElabErrors_boxed_4893_ = (leanh::lean_unbox(v_suppressElabErrors_4889_) as u8);
    v_res_4894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37203__boxed_4892_, v_suppressElabErrors_boxed_4893_, v___x_4890_, v_x_4891_);
    leanh::lean_dec(v_x_4891_);
    leanh::lean_dec_ref(v___x_4890_);
    v_r_4895_ = leanh::lean_box((v_res_4894_) as usize);
    return v_r_4895_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0()
-> f64 {
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: f64 = 0.0;
    v___x_4896_ = leanh::lean_unsigned_to_nat(0);
    v___x_4897_ = lean_float_of_nat(v___x_4896_);
    return v___x_4897_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(
    mut v___x_4899_: u8,
    mut v_as_4900_: *mut leanh::LeanObject,
    mut v_sz_4901_: usize,
    mut v_i_4902_: usize,
    mut v_b_4903_: *mut leanh::LeanObject,
    mut v___y_4904_: *mut leanh::LeanObject,
    mut v___y_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: usize = 0;
    let mut v___x_4910_: usize = 0;
    let mut v___x_4912_: u8 = 0;
    let mut v___x_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4919_: u8 = 0;
    let mut v_fst_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: f64 = 0.0;
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4932_: u8 = 0;
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: u8 = 0;
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keepFullRange_4949_: u8 = 0;
    let mut v_severity_4950_: u8 = 0;
    let mut v_isSilent_4951_: u8 = 0;
    let mut v_caption_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4956_: u8 = 0;
    let mut v_currNamespace_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4970_: u8 = 0;
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4983_: u8 = 0;
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v_data_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: u8 = 0;
    let mut v_reuseFailAlloc_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4912_ = lean_usize_dec_lt(v_i_4902_, v_sz_4901_);
                if v___x_4912_ == 0 {
                    v___x_4913_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4913_, 0, v_b_4903_);
                    return v___x_4913_;
                } else {
                    v_a_4914_ = lean_array_uget(v_as_4900_, v_i_4902_);
                    v_fst_4915_ = leanh::lean_ctor_get(v_a_4914_, 0);
                    v_snd_4916_ = leanh::lean_ctor_get(v_a_4914_, 1);
                    v_isSharedCheck_4992_ = (!leanh::lean_is_exclusive(v_a_4914_)) as u8;
                    if v_isSharedCheck_4992_ == 0 {
                        v___x_4918_ = v_a_4914_;
                        v_isShared_4919_ = v_isSharedCheck_4992_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4916_);
                        leanh::lean_inc(v_fst_4915_);
                        leanh::lean_dec(v_a_4914_);
                        v___x_4918_ = leanh::lean_box(0);
                        v_isShared_4919_ = v_isSharedCheck_4992_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4909_ = 1usize;
                v___x_4910_ = lean_usize_add(v_i_4902_, v___x_4909_);
                v_i_4902_ = v___x_4910_;
                v_b_4903_ = v_a_4908_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_4920_ = leanh::lean_ctor_get(v_fst_4915_, 0);
                v_snd_4921_ = leanh::lean_ctor_get(v_fst_4915_, 1);
                v_isSharedCheck_4991_ = (!leanh::lean_is_exclusive(v_fst_4915_)) as u8;
                if v_isSharedCheck_4991_ == 0 {
                    v___x_4923_ = v_fst_4915_;
                    v_isShared_4924_ = v_isSharedCheck_4991_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4921_);
                    leanh::lean_inc(v_fst_4920_);
                    leanh::lean_dec(v_fst_4915_);
                    v___x_4923_ = leanh::lean_box(0);
                    v_isShared_4924_ = v_isSharedCheck_4991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4925_ = leanh::lean_box(0);
                v___x_4926_ = leanh::lean_box(0);
                v___x_4927_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
                v___x_4928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1;
                v___x_4929_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4929_, 0, v___x_4925_);
                leanh::lean_ctor_set(v___x_4929_, 1, v___x_4926_);
                leanh::lean_ctor_set(v___x_4929_, 2, v___x_4928_);
                leanh::lean_ctor_set_float(
                    v___x_4929_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4927_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4929_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4927_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4929_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4912_,
                );
                v_fileName_4930_ = leanh::lean_ctor_get(v___y_4904_, 0);
                v_fileMap_4931_ = leanh::lean_ctor_get(v___y_4904_, 1);
                v_suppressElabErrors_4932_ = leanh::lean_ctor_get_uint8(
                    v___y_4904_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v___x_4933_ = leanh::lean_box(0);
                v___x_4934_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0;
                v___x_4935_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1;
                v___x_4936_ = l_Lean_MessageData_nil;
                v___x_4937_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4937_, 0, v___x_4929_);
                leanh::lean_ctor_set(v___x_4937_, 1, v___x_4936_);
                leanh::lean_ctor_set(v___x_4937_, 2, v_snd_4916_);
                if v_isShared_4924_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4923_, 8);
                    leanh::lean_ctor_set(v___x_4923_, 1, v___x_4937_);
                    leanh::lean_ctor_set(v___x_4923_, 0, v___x_4935_);
                    v___x_4939_ = v___x_4923_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 1, v___x_4937_);
                    v___x_4939_ = v_reuseFailAlloc_4990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4940_ = 0;
                leanh::lean_inc_ref(v_fileMap_4931_);
                leanh::lean_inc_ref(v_fileName_4930_);
                v___x_4941_ = l_Lean_Elab_mkMessageCore(
                    v_fileName_4930_,
                    v_fileMap_4931_,
                    v___x_4939_,
                    v___x_4940_,
                    v_fst_4920_,
                    v_snd_4921_,
                );
                leanh::lean_dec(v_snd_4921_);
                leanh::lean_dec(v_fst_4920_);
                if v_suppressElabErrors_4932_ == 0 {
                    v___y_4943_ = v___y_4904_;
                    v___y_4944_ = v___y_4905_;
                    state = 5;
                    continue;
                } else {
                    v_data_4985_ = leanh::lean_ctor_get(v___x_4941_, 4);
                    leanh::lean_inc(v_data_4985_);
                    v___x_4986_ = leanh::lean_box((v___x_4899_) as usize);
                    v___x_4987_ = leanh::lean_box((v_suppressElabErrors_4932_) as usize);
                    v___f_4988_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
                    leanh::lean_closure_set(v___f_4988_, 0, v___x_4986_);
                    leanh::lean_closure_set(v___f_4988_, 1, v___x_4987_);
                    leanh::lean_closure_set(v___f_4988_, 2, v___x_4934_);
                    v___x_4989_ = l_Lean_MessageData_hasTag(v___f_4988_, v_data_4985_);
                    if v___x_4989_ == 0 {
                        leanh::lean_dec_ref(v___x_4941_);
                        leanh::lean_del_object(v___x_4918_);
                        v_a_4908_ = v___x_4933_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4943_ = v___y_4904_;
                        v___y_4944_ = v___y_4905_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4945_ = lean_st_ref_take(v___y_4944_);
                v_fileName_4946_ = leanh::lean_ctor_get(v___x_4941_, 0);
                v_pos_4947_ = leanh::lean_ctor_get(v___x_4941_, 1);
                v_endPos_4948_ = leanh::lean_ctor_get(v___x_4941_, 2);
                v_keepFullRange_4949_ = leanh::lean_ctor_get_uint8(
                    v___x_4941_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                );
                v_severity_4950_ = leanh::lean_ctor_get_uint8(
                    v___x_4941_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_isSilent_4951_ = leanh::lean_ctor_get_uint8(
                    v___x_4941_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                );
                v_caption_4952_ = leanh::lean_ctor_get(v___x_4941_, 3);
                v_data_4953_ = leanh::lean_ctor_get(v___x_4941_, 4);
                v_isSharedCheck_4984_ = (!leanh::lean_is_exclusive(v___x_4941_)) as u8;
                if v_isSharedCheck_4984_ == 0 {
                    v___x_4955_ = v___x_4941_;
                    v_isShared_4956_ = v_isSharedCheck_4984_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_data_4953_);
                    leanh::lean_inc(v_caption_4952_);
                    leanh::lean_inc(v_endPos_4948_);
                    leanh::lean_inc(v_pos_4947_);
                    leanh::lean_inc(v_fileName_4946_);
                    leanh::lean_dec(v___x_4941_);
                    v___x_4955_ = leanh::lean_box(0);
                    v_isShared_4956_ = v_isSharedCheck_4984_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_currNamespace_4957_ = leanh::lean_ctor_get(v___y_4943_, 6);
                v_openDecls_4958_ = leanh::lean_ctor_get(v___y_4943_, 7);
                v_env_4959_ = leanh::lean_ctor_get(v___x_4945_, 0);
                v_nextMacroScope_4960_ = leanh::lean_ctor_get(v___x_4945_, 1);
                v_ngen_4961_ = leanh::lean_ctor_get(v___x_4945_, 2);
                v_auxDeclNGen_4962_ = leanh::lean_ctor_get(v___x_4945_, 3);
                v_traceState_4963_ = leanh::lean_ctor_get(v___x_4945_, 4);
                v_cache_4964_ = leanh::lean_ctor_get(v___x_4945_, 5);
                v_messages_4965_ = leanh::lean_ctor_get(v___x_4945_, 6);
                v_infoState_4966_ = leanh::lean_ctor_get(v___x_4945_, 7);
                v_snapshotTasks_4967_ = leanh::lean_ctor_get(v___x_4945_, 8);
                v_isSharedCheck_4983_ = (!leanh::lean_is_exclusive(v___x_4945_)) as u8;
                if v_isSharedCheck_4983_ == 0 {
                    v___x_4969_ = v___x_4945_;
                    v_isShared_4970_ = v_isSharedCheck_4983_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4967_);
                    leanh::lean_inc(v_infoState_4966_);
                    leanh::lean_inc(v_messages_4965_);
                    leanh::lean_inc(v_cache_4964_);
                    leanh::lean_inc(v_traceState_4963_);
                    leanh::lean_inc(v_auxDeclNGen_4962_);
                    leanh::lean_inc(v_ngen_4961_);
                    leanh::lean_inc(v_nextMacroScope_4960_);
                    leanh::lean_inc(v_env_4959_);
                    leanh::lean_dec(v___x_4945_);
                    v___x_4969_ = leanh::lean_box(0);
                    v_isShared_4970_ = v_isSharedCheck_4983_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v_openDecls_4958_);
                leanh::lean_inc(v_currNamespace_4957_);
                if v_isShared_4919_ == 0 {
                    leanh::lean_ctor_set(v___x_4918_, 1, v_openDecls_4958_);
                    leanh::lean_ctor_set(v___x_4918_, 0, v_currNamespace_4957_);
                    v___x_4972_ = v___x_4918_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4982_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_currNamespace_4957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 1, v_openDecls_4958_);
                    v___x_4972_ = v_reuseFailAlloc_4982_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4973_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4973_, 0, v___x_4972_);
                leanh::lean_ctor_set(v___x_4973_, 1, v_data_4953_);
                if v_isShared_4956_ == 0 {
                    leanh::lean_ctor_set(v___x_4955_, 4, v___x_4973_);
                    v___x_4975_ = v___x_4955_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4981_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_fileName_4946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_pos_4947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 2, v_endPos_4948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 3, v_caption_4952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 4, v___x_4973_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4981_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v_keepFullRange_4949_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4981_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v_severity_4950_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4981_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                        v_isSilent_4951_,
                    );
                    v___x_4975_ = v_reuseFailAlloc_4981_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4976_ = l_Lean_MessageLog_add(v___x_4975_, v_messages_4965_);
                if v_isShared_4970_ == 0 {
                    leanh::lean_ctor_set(v___x_4969_, 6, v___x_4976_);
                    v___x_4978_ = v___x_4969_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_env_4959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_nextMacroScope_4960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 2, v_ngen_4961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 3, v_auxDeclNGen_4962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 4, v_traceState_4963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 5, v_cache_4964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 6, v___x_4976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 7, v_infoState_4966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 8, v_snapshotTasks_4967_);
                    v___x_4978_ = v_reuseFailAlloc_4980_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4979_ = lean_st_ref_set(v___y_4944_, v___x_4978_);
                v_a_4908_ = v___x_4933_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(
    mut v___x_4993_: *mut leanh::LeanObject,
    mut v_as_4994_: *mut leanh::LeanObject,
    mut v_sz_4995_: *mut leanh::LeanObject,
    mut v_i_4996_: *mut leanh::LeanObject,
    mut v_b_4997_: *mut leanh::LeanObject,
    mut v___y_4998_: *mut leanh::LeanObject,
    mut v___y_4999_: *mut leanh::LeanObject,
    mut v___y_5000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37276__boxed_5001_: u8 = 0;
    let mut v_sz_boxed_5002_: usize = 0;
    let mut v_i_boxed_5003_: usize = 0;
    let mut v_res_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37276__boxed_5001_ = (leanh::lean_unbox(v___x_4993_) as u8);
    v_sz_boxed_5002_ = leanh::lean_unbox_usize(v_sz_4995_);
    leanh::lean_dec(v_sz_4995_);
    v_i_boxed_5003_ = leanh::lean_unbox_usize(v_i_4996_);
    leanh::lean_dec(v_i_4996_);
    v_res_5004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37276__boxed_5001_, v_as_4994_, v_sz_boxed_5002_, v_i_boxed_5003_, v_b_4997_, v___y_4998_, v___y_4999_);
    leanh::lean_dec(v___y_4999_);
    leanh::lean_dec_ref(v___y_4998_);
    leanh::lean_dec_ref(v_as_4994_);
    return v_res_5004_;
}
pub unsafe fn l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(
    mut v_opts_5005_: *mut leanh::LeanObject,
    mut v_opt_5006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5014_: u8 = 0;
    let mut v_v_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_5007_ = leanh::lean_ctor_get(v_opt_5006_, 0);
                v_map_5008_ = leanh::lean_ctor_get(v_opts_5005_, 0);
                v___x_5009_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5008_, v_name_5007_);
                if leanh::lean_obj_tag(v___x_5009_) == 0 {
                    v___x_5010_ = leanh::lean_box(0);
                    return v___x_5010_;
                } else {
                    v_val_5011_ = leanh::lean_ctor_get(v___x_5009_, 0);
                    v_isSharedCheck_5020_ = (!leanh::lean_is_exclusive(v___x_5009_)) as u8;
                    if v_isSharedCheck_5020_ == 0 {
                        v___x_5013_ = v___x_5009_;
                        v_isShared_5014_ = v_isSharedCheck_5020_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5011_);
                        leanh::lean_dec(v___x_5009_);
                        v___x_5013_ = leanh::lean_box(0);
                        v_isShared_5014_ = v_isSharedCheck_5020_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_val_5011_) == 0 {
                    v_v_5015_ = leanh::lean_ctor_get(v_val_5011_, 0);
                    leanh::lean_inc_ref(v_v_5015_);
                    leanh::lean_dec_ref_known(v_val_5011_, 1);
                    if v_isShared_5014_ == 0 {
                        leanh::lean_ctor_set(v___x_5013_, 0, v_v_5015_);
                        v___x_5017_ = v___x_5013_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_v_5015_);
                        v___x_5017_ = v_reuseFailAlloc_5018_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5013_);
                    leanh::lean_dec(v_val_5011_);
                    v___x_5019_ = leanh::lean_box(0);
                    return v___x_5019_;
                }
            }
            2 => {
                return v___x_5017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(
    mut v_opts_5021_: *mut leanh::LeanObject,
    mut v_opt_5022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5023_ =
        l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(
            v_opts_5021_,
            v_opt_5022_,
        );
    leanh::lean_dec_ref(v_opt_5022_);
    leanh::lean_dec_ref(v_opts_5021_);
    return v_res_5023_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(
    mut v_a_5024_: *mut leanh::LeanObject,
    mut v_fallback_5025_: *mut leanh::LeanObject,
    mut v_x_5026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5031_: u8 = 0;
    let mut v_fst_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5026_) == 0 {
                    leanh::lean_inc(v_fallback_5025_);
                    return v_fallback_5025_;
                } else {
                    v_key_5027_ = leanh::lean_ctor_get(v_x_5026_, 0);
                    v_value_5028_ = leanh::lean_ctor_get(v_x_5026_, 1);
                    v_tail_5029_ = leanh::lean_ctor_get(v_x_5026_, 2);
                    v_fst_5033_ = leanh::lean_ctor_get(v_key_5027_, 0);
                    v_snd_5034_ = leanh::lean_ctor_get(v_key_5027_, 1);
                    v_fst_5035_ = leanh::lean_ctor_get(v_a_5024_, 0);
                    v_snd_5036_ = leanh::lean_ctor_get(v_a_5024_, 1);
                    v___x_5037_ = lean_nat_dec_eq(v_fst_5033_, v_fst_5035_);
                    if v___x_5037_ == 0 {
                        v___y_5031_ = v___x_5037_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5038_ = lean_nat_dec_eq(v_snd_5034_, v_snd_5036_);
                        v___y_5031_ = v___x_5038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5031_ == 0 {
                    v_x_5026_ = v_tail_5029_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_value_5028_);
                    return v_value_5028_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(
    mut v_a_5039_: *mut leanh::LeanObject,
    mut v_fallback_5040_: *mut leanh::LeanObject,
    mut v_x_5041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5042_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_5039_, v_fallback_5040_, v_x_5041_);
    leanh::lean_dec(v_x_5041_);
    leanh::lean_dec(v_fallback_5040_);
    leanh::lean_dec_ref(v_a_5039_);
    return v_res_5042_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(
    mut v_m_5043_: *mut leanh::LeanObject,
    mut v_a_5044_: *mut leanh::LeanObject,
    mut v_fallback_5045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: u64 = 0;
    let mut v___x_5051_: u64 = 0;
    let mut v___x_5052_: u64 = 0;
    let mut v___x_5053_: u64 = 0;
    let mut v___x_5054_: u64 = 0;
    let mut v_fold_5055_: u64 = 0;
    let mut v___x_5056_: u64 = 0;
    let mut v___x_5057_: u64 = 0;
    let mut v___x_5058_: u64 = 0;
    let mut v___x_5059_: usize = 0;
    let mut v___x_5060_: usize = 0;
    let mut v___x_5061_: usize = 0;
    let mut v___x_5062_: usize = 0;
    let mut v___x_5063_: usize = 0;
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5046_ = leanh::lean_ctor_get(v_m_5043_, 1);
    v_fst_5047_ = leanh::lean_ctor_get(v_a_5044_, 0);
    v_snd_5048_ = leanh::lean_ctor_get(v_a_5044_, 1);
    v___x_5049_ = lean_array_get_size(v_buckets_5046_);
    v___x_5050_ = l_String_instHashableRaw_hash(v_fst_5047_);
    v___x_5051_ = l_String_instHashableRaw_hash(v_snd_5048_);
    v___x_5052_ = lean_uint64_mix_hash(v___x_5050_, v___x_5051_);
    v___x_5053_ = 32u64;
    v___x_5054_ = lean_uint64_shift_right(v___x_5052_, v___x_5053_);
    v_fold_5055_ = lean_uint64_xor(v___x_5052_, v___x_5054_);
    v___x_5056_ = 16u64;
    v___x_5057_ = lean_uint64_shift_right(v_fold_5055_, v___x_5056_);
    v___x_5058_ = lean_uint64_xor(v_fold_5055_, v___x_5057_);
    v___x_5059_ = lean_uint64_to_usize(v___x_5058_);
    v___x_5060_ = lean_usize_of_nat(v___x_5049_);
    v___x_5061_ = 1usize;
    v___x_5062_ = lean_usize_sub(v___x_5060_, v___x_5061_);
    v___x_5063_ = lean_usize_land(v___x_5059_, v___x_5062_);
    v___x_5064_ = lean_array_uget_borrowed(v_buckets_5046_, v___x_5063_);
    v___x_5065_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_5044_, v_fallback_5045_, v___x_5064_);
    return v___x_5065_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(
    mut v_m_5066_: *mut leanh::LeanObject,
    mut v_a_5067_: *mut leanh::LeanObject,
    mut v_fallback_5068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_5066_, v_a_5067_, v_fallback_5068_);
    leanh::lean_dec(v_fallback_5068_);
    leanh::lean_dec_ref(v_a_5067_);
    leanh::lean_dec_ref(v_m_5066_);
    return v_res_5069_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(
    mut v_x_5070_: *mut leanh::LeanObject,
    mut v_x_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5077_: u8 = 0;
    let mut v_fst_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: u64 = 0;
    let mut v___x_5082_: u64 = 0;
    let mut v___x_5083_: u64 = 0;
    let mut v___x_5084_: u64 = 0;
    let mut v___x_5085_: u64 = 0;
    let mut v_fold_5086_: u64 = 0;
    let mut v___x_5087_: u64 = 0;
    let mut v___x_5088_: u64 = 0;
    let mut v___x_5089_: u64 = 0;
    let mut v___x_5090_: usize = 0;
    let mut v___x_5091_: usize = 0;
    let mut v___x_5092_: usize = 0;
    let mut v___x_5093_: usize = 0;
    let mut v___x_5094_: usize = 0;
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5071_) == 0 {
                    return v_x_5070_;
                } else {
                    v_key_5072_ = leanh::lean_ctor_get(v_x_5071_, 0);
                    v_value_5073_ = leanh::lean_ctor_get(v_x_5071_, 1);
                    v_tail_5074_ = leanh::lean_ctor_get(v_x_5071_, 2);
                    v_isSharedCheck_5101_ = (!leanh::lean_is_exclusive(v_x_5071_)) as u8;
                    if v_isSharedCheck_5101_ == 0 {
                        v___x_5076_ = v_x_5071_;
                        v_isShared_5077_ = v_isSharedCheck_5101_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5074_);
                        leanh::lean_inc(v_value_5073_);
                        leanh::lean_inc(v_key_5072_);
                        leanh::lean_dec(v_x_5071_);
                        v___x_5076_ = leanh::lean_box(0);
                        v_isShared_5077_ = v_isSharedCheck_5101_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5078_ = leanh::lean_ctor_get(v_key_5072_, 0);
                v_snd_5079_ = leanh::lean_ctor_get(v_key_5072_, 1);
                v___x_5080_ = lean_array_get_size(v_x_5070_);
                v___x_5081_ = l_String_instHashableRaw_hash(v_fst_5078_);
                v___x_5082_ = l_String_instHashableRaw_hash(v_snd_5079_);
                v___x_5083_ = lean_uint64_mix_hash(v___x_5081_, v___x_5082_);
                v___x_5084_ = 32u64;
                v___x_5085_ = lean_uint64_shift_right(v___x_5083_, v___x_5084_);
                v_fold_5086_ = lean_uint64_xor(v___x_5083_, v___x_5085_);
                v___x_5087_ = 16u64;
                v___x_5088_ = lean_uint64_shift_right(v_fold_5086_, v___x_5087_);
                v___x_5089_ = lean_uint64_xor(v_fold_5086_, v___x_5088_);
                v___x_5090_ = lean_uint64_to_usize(v___x_5089_);
                v___x_5091_ = lean_usize_of_nat(v___x_5080_);
                v___x_5092_ = 1usize;
                v___x_5093_ = lean_usize_sub(v___x_5091_, v___x_5092_);
                v___x_5094_ = lean_usize_land(v___x_5090_, v___x_5093_);
                v___x_5095_ = lean_array_uget_borrowed(v_x_5070_, v___x_5094_);
                leanh::lean_inc(v___x_5095_);
                if v_isShared_5077_ == 0 {
                    leanh::lean_ctor_set(v___x_5076_, 2, v___x_5095_);
                    v___x_5097_ = v___x_5076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5100_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_key_5072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5100_, 1, v_value_5073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5100_, 2, v___x_5095_);
                    v___x_5097_ = v_reuseFailAlloc_5100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5098_ = lean_array_uset(v_x_5070_, v___x_5094_, v___x_5097_);
                v_x_5070_ = v___x_5098_;
                v_x_5071_ = v_tail_5074_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(
    mut v_i_5102_: *mut leanh::LeanObject,
    mut v_source_5103_: *mut leanh::LeanObject,
    mut v_target_5104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: u8 = 0;
    let mut v_es_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5105_ = lean_array_get_size(v_source_5103_);
                v___x_5106_ = lean_nat_dec_lt(v_i_5102_, v___x_5105_);
                if v___x_5106_ == 0 {
                    leanh::lean_dec_ref(v_source_5103_);
                    leanh::lean_dec(v_i_5102_);
                    return v_target_5104_;
                } else {
                    v_es_5107_ = lean_array_fget(v_source_5103_, v_i_5102_);
                    v___x_5108_ = leanh::lean_box(0);
                    v_source_5109_ = lean_array_fset(v_source_5103_, v_i_5102_, v___x_5108_);
                    v_target_5110_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_5104_, v_es_5107_);
                    v___x_5111_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5112_ = lean_nat_add(v_i_5102_, v___x_5111_);
                    leanh::lean_dec(v_i_5102_);
                    v_i_5102_ = v___x_5112_;
                    v_source_5103_ = v_source_5109_;
                    v_target_5104_ = v_target_5110_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(
    mut v_data_5114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5115_ = lean_array_get_size(v_data_5114_);
    v___x_5116_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5117_ = lean_nat_mul(v___x_5115_, v___x_5116_);
    v___x_5118_ = leanh::lean_unsigned_to_nat(0);
    v___x_5119_ = leanh::lean_box(0);
    v___x_5120_ = lean_mk_array(v_nbuckets_5117_, v___x_5119_);
    v___x_5121_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_5118_, v_data_5114_, v___x_5120_);
    return v___x_5121_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(
    mut v_a_5122_: *mut leanh::LeanObject,
    mut v_b_5123_: *mut leanh::LeanObject,
    mut v_x_5124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5130_: u8 = 0;
    let mut v___y_5132_: u8 = 0;
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: u8 = 0;
    let mut v___x_5145_: u8 = 0;
    let mut v_isSharedCheck_5146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5124_) == 0 {
                    leanh::lean_dec(v_b_5123_);
                    leanh::lean_dec_ref(v_a_5122_);
                    return v_x_5124_;
                } else {
                    v_key_5125_ = leanh::lean_ctor_get(v_x_5124_, 0);
                    v_value_5126_ = leanh::lean_ctor_get(v_x_5124_, 1);
                    v_tail_5127_ = leanh::lean_ctor_get(v_x_5124_, 2);
                    v_isSharedCheck_5146_ = (!leanh::lean_is_exclusive(v_x_5124_)) as u8;
                    if v_isSharedCheck_5146_ == 0 {
                        v___x_5129_ = v_x_5124_;
                        v_isShared_5130_ = v_isSharedCheck_5146_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5127_);
                        leanh::lean_inc(v_value_5126_);
                        leanh::lean_inc(v_key_5125_);
                        leanh::lean_dec(v_x_5124_);
                        v___x_5129_ = leanh::lean_box(0);
                        v_isShared_5130_ = v_isSharedCheck_5146_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5140_ = leanh::lean_ctor_get(v_key_5125_, 0);
                v_snd_5141_ = leanh::lean_ctor_get(v_key_5125_, 1);
                v_fst_5142_ = leanh::lean_ctor_get(v_a_5122_, 0);
                v_snd_5143_ = leanh::lean_ctor_get(v_a_5122_, 1);
                v___x_5144_ = lean_nat_dec_eq(v_fst_5140_, v_fst_5142_);
                if v___x_5144_ == 0 {
                    v___y_5132_ = v___x_5144_;
                    state = 2;
                    continue;
                } else {
                    v___x_5145_ = lean_nat_dec_eq(v_snd_5141_, v_snd_5143_);
                    v___y_5132_ = v___x_5145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_5132_ == 0 {
                    v___x_5133_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_5122_, v_b_5123_, v_tail_5127_);
                    if v_isShared_5130_ == 0 {
                        leanh::lean_ctor_set(v___x_5129_, 2, v___x_5133_);
                        v___x_5135_ = v___x_5129_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5136_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_key_5125_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 1, v_value_5126_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 2, v___x_5133_);
                        v___x_5135_ = v_reuseFailAlloc_5136_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_5126_);
                    leanh::lean_dec(v_key_5125_);
                    if v_isShared_5130_ == 0 {
                        leanh::lean_ctor_set(v___x_5129_, 1, v_b_5123_);
                        leanh::lean_ctor_set(v___x_5129_, 0, v_a_5122_);
                        v___x_5138_ = v___x_5129_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5139_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5122_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 1, v_b_5123_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 2, v_tail_5127_);
                        v___x_5138_ = v_reuseFailAlloc_5139_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5135_;
            }
            4 => {
                return v___x_5138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(
    mut v_a_5147_: *mut leanh::LeanObject,
    mut v_x_5148_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5149_: u8 = 0;
    let mut v_key_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5153_: u8 = 0;
    let mut v_fst_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5148_) == 0 {
                    v___x_5149_ = 0;
                    return v___x_5149_;
                } else {
                    v_key_5150_ = leanh::lean_ctor_get(v_x_5148_, 0);
                    v_tail_5151_ = leanh::lean_ctor_get(v_x_5148_, 2);
                    v_fst_5155_ = leanh::lean_ctor_get(v_key_5150_, 0);
                    v_snd_5156_ = leanh::lean_ctor_get(v_key_5150_, 1);
                    v_fst_5157_ = leanh::lean_ctor_get(v_a_5147_, 0);
                    v_snd_5158_ = leanh::lean_ctor_get(v_a_5147_, 1);
                    v___x_5159_ = lean_nat_dec_eq(v_fst_5155_, v_fst_5157_);
                    if v___x_5159_ == 0 {
                        v___y_5153_ = v___x_5159_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5160_ = lean_nat_dec_eq(v_snd_5156_, v_snd_5158_);
                        v___y_5153_ = v___x_5160_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5153_ == 0 {
                    v_x_5148_ = v_tail_5151_;
                    state = 0;
                    continue;
                } else {
                    return v___y_5153_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(
    mut v_a_5161_: *mut leanh::LeanObject,
    mut v_x_5162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5163_: u8 = 0;
    let mut v_r_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_5161_, v_x_5162_);
    leanh::lean_dec(v_x_5162_);
    leanh::lean_dec_ref(v_a_5161_);
    v_r_5164_ = leanh::lean_box((v_res_5163_) as usize);
    return v_r_5164_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(
    mut v_m_5165_: *mut leanh::LeanObject,
    mut v_a_5166_: *mut leanh::LeanObject,
    mut v_b_5167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5172_: u8 = 0;
    let mut v_fst_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: u64 = 0;
    let mut v___x_5177_: u64 = 0;
    let mut v___x_5178_: u64 = 0;
    let mut v___x_5179_: u64 = 0;
    let mut v___x_5180_: u64 = 0;
    let mut v_fold_5181_: u64 = 0;
    let mut v___x_5182_: u64 = 0;
    let mut v___x_5183_: u64 = 0;
    let mut v___x_5184_: u64 = 0;
    let mut v___x_5185_: usize = 0;
    let mut v___x_5186_: usize = 0;
    let mut v___x_5187_: usize = 0;
    let mut v___x_5188_: usize = 0;
    let mut v___x_5189_: usize = 0;
    let mut v_bkt_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: u8 = 0;
    let mut v_val_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5168_ = leanh::lean_ctor_get(v_m_5165_, 0);
                v_buckets_5169_ = leanh::lean_ctor_get(v_m_5165_, 1);
                v_isSharedCheck_5216_ = (!leanh::lean_is_exclusive(v_m_5165_)) as u8;
                if v_isSharedCheck_5216_ == 0 {
                    v___x_5171_ = v_m_5165_;
                    v_isShared_5172_ = v_isSharedCheck_5216_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_5169_);
                    leanh::lean_inc(v_size_5168_);
                    leanh::lean_dec(v_m_5165_);
                    v___x_5171_ = leanh::lean_box(0);
                    v_isShared_5172_ = v_isSharedCheck_5216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5173_ = leanh::lean_ctor_get(v_a_5166_, 0);
                v_snd_5174_ = leanh::lean_ctor_get(v_a_5166_, 1);
                v___x_5175_ = lean_array_get_size(v_buckets_5169_);
                v___x_5176_ = l_String_instHashableRaw_hash(v_fst_5173_);
                v___x_5177_ = l_String_instHashableRaw_hash(v_snd_5174_);
                v___x_5178_ = lean_uint64_mix_hash(v___x_5176_, v___x_5177_);
                v___x_5179_ = 32u64;
                v___x_5180_ = lean_uint64_shift_right(v___x_5178_, v___x_5179_);
                v_fold_5181_ = lean_uint64_xor(v___x_5178_, v___x_5180_);
                v___x_5182_ = 16u64;
                v___x_5183_ = lean_uint64_shift_right(v_fold_5181_, v___x_5182_);
                v___x_5184_ = lean_uint64_xor(v_fold_5181_, v___x_5183_);
                v___x_5185_ = lean_uint64_to_usize(v___x_5184_);
                v___x_5186_ = lean_usize_of_nat(v___x_5175_);
                v___x_5187_ = 1usize;
                v___x_5188_ = lean_usize_sub(v___x_5186_, v___x_5187_);
                v___x_5189_ = lean_usize_land(v___x_5185_, v___x_5188_);
                v_bkt_5190_ = lean_array_uget_borrowed(v_buckets_5169_, v___x_5189_);
                v___x_5191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_5166_, v_bkt_5190_);
                if v___x_5191_ == 0 {
                    v___x_5192_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5193_ = lean_nat_add(v_size_5168_, v___x_5192_);
                    leanh::lean_dec(v_size_5168_);
                    leanh::lean_inc(v_bkt_5190_);
                    v___x_5194_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5194_, 0, v_a_5166_);
                    leanh::lean_ctor_set(v___x_5194_, 1, v_b_5167_);
                    leanh::lean_ctor_set(v___x_5194_, 2, v_bkt_5190_);
                    v_buckets_x27_5195_ =
                        lean_array_uset(v_buckets_5169_, v___x_5189_, v___x_5194_);
                    v___x_5196_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5197_ = lean_nat_mul(v_size_x27_5193_, v___x_5196_);
                    v___x_5198_ = leanh::lean_unsigned_to_nat(3);
                    v___x_5199_ = lean_nat_div(v___x_5197_, v___x_5198_);
                    leanh::lean_dec(v___x_5197_);
                    v___x_5200_ = lean_array_get_size(v_buckets_x27_5195_);
                    v___x_5201_ = lean_nat_dec_le(v___x_5199_, v___x_5200_);
                    leanh::lean_dec(v___x_5199_);
                    if v___x_5201_ == 0 {
                        v_val_5202_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_5195_);
                        if v_isShared_5172_ == 0 {
                            leanh::lean_ctor_set(v___x_5171_, 1, v_val_5202_);
                            leanh::lean_ctor_set(v___x_5171_, 0, v_size_x27_5193_);
                            v___x_5204_ = v___x_5171_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5205_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5205_,
                                0,
                                v_size_x27_5193_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_5205_, 1, v_val_5202_);
                            v___x_5204_ = v_reuseFailAlloc_5205_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5172_ == 0 {
                            leanh::lean_ctor_set(v___x_5171_, 1, v_buckets_x27_5195_);
                            leanh::lean_ctor_set(v___x_5171_, 0, v_size_x27_5193_);
                            v___x_5207_ = v___x_5171_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5208_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5208_,
                                0,
                                v_size_x27_5193_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5208_,
                                1,
                                v_buckets_x27_5195_,
                            );
                            v___x_5207_ = v_reuseFailAlloc_5208_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_5190_);
                    v___x_5209_ = leanh::lean_box(0);
                    v_buckets_x27_5210_ =
                        lean_array_uset(v_buckets_5169_, v___x_5189_, v___x_5209_);
                    v___x_5211_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_5166_, v_b_5167_, v_bkt_5190_);
                    v___x_5212_ = lean_array_uset(v_buckets_x27_5210_, v___x_5189_, v___x_5211_);
                    if v_isShared_5172_ == 0 {
                        leanh::lean_ctor_set(v___x_5171_, 1, v___x_5212_);
                        v___x_5214_ = v___x_5171_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5215_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_size_5168_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5215_, 1, v___x_5212_);
                        v___x_5214_ = v_reuseFailAlloc_5215_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5204_;
            }
            3 => {
                return v___x_5207_;
            }
            4 => {
                return v___x_5214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(
    mut v___x_5219_: u8,
    mut v_as_5220_: *mut leanh::LeanObject,
    mut v_sz_5221_: usize,
    mut v_i_5222_: usize,
    mut v_b_5223_: *mut leanh::LeanObject,
    mut v___y_5224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5226_: u8 = 0;
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5231_: u8 = 0;
    let mut v_ref_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: usize = 0;
    let mut v___x_5252_: usize = 0;
    let mut v_reuseFailAlloc_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut v_unused_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5226_ = lean_usize_dec_lt(v_i_5222_, v_sz_5221_);
                if v___x_5226_ == 0 {
                    v___x_5227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5227_, 0, v_b_5223_);
                    return v___x_5227_;
                } else {
                    v_snd_5228_ = leanh::lean_ctor_get(v_b_5223_, 1);
                    v_isSharedCheck_5265_ = (!leanh::lean_is_exclusive(v_b_5223_)) as u8;
                    if v_isSharedCheck_5265_ == 0 {
                        v_unused_5266_ = leanh::lean_ctor_get(v_b_5223_, 0);
                        leanh::lean_dec(v_unused_5266_);
                        v___x_5230_ = v_b_5223_;
                        v_isShared_5231_ = v_isSharedCheck_5265_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5228_);
                        leanh::lean_dec(v_b_5223_);
                        v___x_5230_ = leanh::lean_box(0);
                        v_isShared_5231_ = v_isSharedCheck_5265_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_5232_ = leanh::lean_ctor_get(v___y_5224_, 5);
                v_a_5233_ = lean_array_uget(v_as_5220_, v_i_5222_);
                v_ref_5234_ = leanh::lean_ctor_get(v_a_5233_, 0);
                v_msg_5235_ = leanh::lean_ctor_get(v_a_5233_, 1);
                v_isSharedCheck_5264_ = (!leanh::lean_is_exclusive(v_a_5233_)) as u8;
                if v_isSharedCheck_5264_ == 0 {
                    v___x_5237_ = v_a_5233_;
                    v_isShared_5238_ = v_isSharedCheck_5264_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_msg_5235_);
                    leanh::lean_inc(v_ref_5234_);
                    leanh::lean_dec(v_a_5233_);
                    v___x_5237_ = leanh::lean_box(0);
                    v_isShared_5238_ = v_isSharedCheck_5264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5239_ = leanh::lean_box(0);
                v_ref_5256_ = l_Lean_replaceRef(v_ref_5234_, v_ref_5232_);
                leanh::lean_dec(v_ref_5234_);
                v___x_5261_ = l_Lean_Syntax_getPos_x3f(v_ref_5256_, v___x_5219_);
                if leanh::lean_obj_tag(v___x_5261_) == 0 {
                    v___x_5262_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5258_ = v___x_5262_;
                    state = 6;
                    continue;
                } else {
                    v_val_5263_ = leanh::lean_ctor_get(v___x_5261_, 0);
                    leanh::lean_inc(v_val_5263_);
                    leanh::lean_dec_ref_known(v___x_5261_, 1);
                    v___y_5258_ = v_val_5263_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                if v_isShared_5231_ == 0 {
                    leanh::lean_ctor_set(v___x_5230_, 1, v___y_5242_);
                    leanh::lean_ctor_set(v___x_5230_, 0, v___y_5241_);
                    v___x_5244_ = v___x_5230_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5255_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___y_5241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 1, v___y_5242_);
                    v___x_5244_ = v_reuseFailAlloc_5255_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0;
                v___x_5246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_5228_, v___x_5244_, v___x_5245_);
                v___x_5247_ = lean_array_push(v___x_5246_, v_msg_5235_);
                v_pos2traces_5248_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_5228_, v___x_5244_, v___x_5247_);
                if v_isShared_5238_ == 0 {
                    leanh::lean_ctor_set(v___x_5237_, 1, v_pos2traces_5248_);
                    leanh::lean_ctor_set(v___x_5237_, 0, v___x_5239_);
                    v___x_5250_ = v___x_5237_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_pos2traces_5248_);
                    v___x_5250_ = v_reuseFailAlloc_5254_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5251_ = 1usize;
                v___x_5252_ = lean_usize_add(v_i_5222_, v___x_5251_);
                v_i_5222_ = v___x_5252_;
                v_b_5223_ = v___x_5250_;
                state = 0;
                continue;
            }
            6 => {
                v___x_5259_ = l_Lean_Syntax_getTailPos_x3f(v_ref_5256_, v___x_5219_);
                leanh::lean_dec(v_ref_5256_);
                if leanh::lean_obj_tag(v___x_5259_) == 0 {
                    leanh::lean_inc(v___y_5258_);
                    v___y_5241_ = v___y_5258_;
                    v___y_5242_ = v___y_5258_;
                    state = 3;
                    continue;
                } else {
                    v_val_5260_ = leanh::lean_ctor_get(v___x_5259_, 0);
                    leanh::lean_inc(v_val_5260_);
                    leanh::lean_dec_ref_known(v___x_5259_, 1);
                    v___y_5241_ = v___y_5258_;
                    v___y_5242_ = v_val_5260_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(
    mut v___x_5267_: *mut leanh::LeanObject,
    mut v_as_5268_: *mut leanh::LeanObject,
    mut v_sz_5269_: *mut leanh::LeanObject,
    mut v_i_5270_: *mut leanh::LeanObject,
    mut v_b_5271_: *mut leanh::LeanObject,
    mut v___y_5272_: *mut leanh::LeanObject,
    mut v___y_5273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37756__boxed_5274_: u8 = 0;
    let mut v_sz_boxed_5275_: usize = 0;
    let mut v_i_boxed_5276_: usize = 0;
    let mut v_res_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37756__boxed_5274_ = (leanh::lean_unbox(v___x_5267_) as u8);
    v_sz_boxed_5275_ = leanh::lean_unbox_usize(v_sz_5269_);
    leanh::lean_dec(v_sz_5269_);
    v_i_boxed_5276_ = leanh::lean_unbox_usize(v_i_5270_);
    leanh::lean_dec(v_i_5270_);
    v_res_5277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37756__boxed_5274_, v_as_5268_, v_sz_boxed_5275_, v_i_boxed_5276_, v_b_5271_, v___y_5272_);
    leanh::lean_dec_ref(v___y_5272_);
    leanh::lean_dec_ref(v_as_5268_);
    return v_res_5277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(
    mut v___x_5278_: u8,
    mut v_as_5279_: *mut leanh::LeanObject,
    mut v_sz_5280_: usize,
    mut v_i_5281_: usize,
    mut v_b_5282_: *mut leanh::LeanObject,
    mut v___y_5283_: *mut leanh::LeanObject,
    mut v___y_5284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v_ref_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: usize = 0;
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v_unused_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5286_ = lean_usize_dec_lt(v_i_5281_, v_sz_5280_);
                if v___x_5286_ == 0 {
                    v___x_5287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5287_, 0, v_b_5282_);
                    return v___x_5287_;
                } else {
                    v_snd_5288_ = leanh::lean_ctor_get(v_b_5282_, 1);
                    v_isSharedCheck_5325_ = (!leanh::lean_is_exclusive(v_b_5282_)) as u8;
                    if v_isSharedCheck_5325_ == 0 {
                        v_unused_5326_ = leanh::lean_ctor_get(v_b_5282_, 0);
                        leanh::lean_dec(v_unused_5326_);
                        v___x_5290_ = v_b_5282_;
                        v_isShared_5291_ = v_isSharedCheck_5325_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5288_);
                        leanh::lean_dec(v_b_5282_);
                        v___x_5290_ = leanh::lean_box(0);
                        v_isShared_5291_ = v_isSharedCheck_5325_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_5292_ = leanh::lean_ctor_get(v___y_5283_, 5);
                v_a_5293_ = lean_array_uget(v_as_5279_, v_i_5281_);
                v_ref_5294_ = leanh::lean_ctor_get(v_a_5293_, 0);
                v_msg_5295_ = leanh::lean_ctor_get(v_a_5293_, 1);
                v_isSharedCheck_5324_ = (!leanh::lean_is_exclusive(v_a_5293_)) as u8;
                if v_isSharedCheck_5324_ == 0 {
                    v___x_5297_ = v_a_5293_;
                    v_isShared_5298_ = v_isSharedCheck_5324_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_msg_5295_);
                    leanh::lean_inc(v_ref_5294_);
                    leanh::lean_dec(v_a_5293_);
                    v___x_5297_ = leanh::lean_box(0);
                    v_isShared_5298_ = v_isSharedCheck_5324_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5299_ = leanh::lean_box(0);
                v_ref_5316_ = l_Lean_replaceRef(v_ref_5294_, v_ref_5292_);
                leanh::lean_dec(v_ref_5294_);
                v___x_5321_ = l_Lean_Syntax_getPos_x3f(v_ref_5316_, v___x_5278_);
                if leanh::lean_obj_tag(v___x_5321_) == 0 {
                    v___x_5322_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5318_ = v___x_5322_;
                    state = 6;
                    continue;
                } else {
                    v_val_5323_ = leanh::lean_ctor_get(v___x_5321_, 0);
                    leanh::lean_inc(v_val_5323_);
                    leanh::lean_dec_ref_known(v___x_5321_, 1);
                    v___y_5318_ = v_val_5323_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                if v_isShared_5291_ == 0 {
                    leanh::lean_ctor_set(v___x_5290_, 1, v___y_5302_);
                    leanh::lean_ctor_set(v___x_5290_, 0, v___y_5301_);
                    v___x_5304_ = v___x_5290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___y_5301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 1, v___y_5302_);
                    v___x_5304_ = v_reuseFailAlloc_5315_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0;
                v___x_5306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_5288_, v___x_5304_, v___x_5305_);
                v___x_5307_ = lean_array_push(v___x_5306_, v_msg_5295_);
                v_pos2traces_5308_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_5288_, v___x_5304_, v___x_5307_);
                if v_isShared_5298_ == 0 {
                    leanh::lean_ctor_set(v___x_5297_, 1, v_pos2traces_5308_);
                    leanh::lean_ctor_set(v___x_5297_, 0, v___x_5299_);
                    v___x_5310_ = v___x_5297_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5314_, 1, v_pos2traces_5308_);
                    v___x_5310_ = v_reuseFailAlloc_5314_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5311_ = 1usize;
                v___x_5312_ = lean_usize_add(v_i_5281_, v___x_5311_);
                v___x_5313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_5278_, v_as_5279_, v_sz_5280_, v___x_5312_, v___x_5310_, v___y_5283_);
                return v___x_5313_;
            }
            6 => {
                v___x_5319_ = l_Lean_Syntax_getTailPos_x3f(v_ref_5316_, v___x_5278_);
                leanh::lean_dec(v_ref_5316_);
                if leanh::lean_obj_tag(v___x_5319_) == 0 {
                    leanh::lean_inc(v___y_5318_);
                    v___y_5301_ = v___y_5318_;
                    v___y_5302_ = v___y_5318_;
                    state = 3;
                    continue;
                } else {
                    v_val_5320_ = leanh::lean_ctor_get(v___x_5319_, 0);
                    leanh::lean_inc(v_val_5320_);
                    leanh::lean_dec_ref_known(v___x_5319_, 1);
                    v___y_5301_ = v___y_5318_;
                    v___y_5302_ = v_val_5320_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(
    mut v___x_5327_: *mut leanh::LeanObject,
    mut v_as_5328_: *mut leanh::LeanObject,
    mut v_sz_5329_: *mut leanh::LeanObject,
    mut v_i_5330_: *mut leanh::LeanObject,
    mut v_b_5331_: *mut leanh::LeanObject,
    mut v___y_5332_: *mut leanh::LeanObject,
    mut v___y_5333_: *mut leanh::LeanObject,
    mut v___y_5334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37837__boxed_5335_: u8 = 0;
    let mut v_sz_boxed_5336_: usize = 0;
    let mut v_i_boxed_5337_: usize = 0;
    let mut v_res_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37837__boxed_5335_ = (leanh::lean_unbox(v___x_5327_) as u8);
    v_sz_boxed_5336_ = leanh::lean_unbox_usize(v_sz_5329_);
    leanh::lean_dec(v_sz_5329_);
    v_i_boxed_5337_ = leanh::lean_unbox_usize(v_i_5330_);
    leanh::lean_dec(v_i_5330_);
    v_res_5338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37837__boxed_5335_, v_as_5328_, v_sz_boxed_5336_, v_i_boxed_5337_, v_b_5331_, v___y_5332_, v___y_5333_);
    leanh::lean_dec(v___y_5333_);
    leanh::lean_dec_ref(v___y_5332_);
    leanh::lean_dec_ref(v_as_5328_);
    return v_res_5338_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(
    mut v_init_5339_: *mut leanh::LeanObject,
    mut v___x_5340_: u8,
    mut v_n_5341_: *mut leanh::LeanObject,
    mut v_b_5342_: *mut leanh::LeanObject,
    mut v___y_5343_: *mut leanh::LeanObject,
    mut v___y_5344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5349_: usize = 0;
    let mut v___x_5350_: usize = 0;
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v_fst_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5366_: u8 = 0;
    let mut v_a_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5370_: u8 = 0;
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_vs_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5378_: usize = 0;
    let mut v___x_5379_: usize = 0;
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5384_: u8 = 0;
    let mut v_fst_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut v_a_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_5341_) == 0 {
                    v_cs_5346_ = leanh::lean_ctor_get(v_n_5341_, 0);
                    v___x_5347_ = leanh::lean_box(0);
                    v___x_5348_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5348_, 0, v___x_5347_);
                    leanh::lean_ctor_set(v___x_5348_, 1, v_b_5342_);
                    v_sz_5349_ = lean_array_size(v_cs_5346_);
                    v___x_5350_ = 0usize;
                    v___x_5351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_5339_, v___x_5340_, v_cs_5346_, v_sz_5349_, v___x_5350_, v___x_5348_, v___y_5343_, v___y_5344_);
                    if leanh::lean_obj_tag(v___x_5351_) == 0 {
                        v_a_5352_ = leanh::lean_ctor_get(v___x_5351_, 0);
                        v_isSharedCheck_5366_ =
                            (!leanh::lean_is_exclusive(v___x_5351_)) as u8;
                        if v_isSharedCheck_5366_ == 0 {
                            v___x_5354_ = v___x_5351_;
                            v_isShared_5355_ = v_isSharedCheck_5366_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5352_);
                            leanh::lean_dec(v___x_5351_);
                            v___x_5354_ = leanh::lean_box(0);
                            v_isShared_5355_ = v_isSharedCheck_5366_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5367_ = leanh::lean_ctor_get(v___x_5351_, 0);
                        v_isSharedCheck_5374_ =
                            (!leanh::lean_is_exclusive(v___x_5351_)) as u8;
                        if v_isSharedCheck_5374_ == 0 {
                            v___x_5369_ = v___x_5351_;
                            v_isShared_5370_ = v_isSharedCheck_5374_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5367_);
                            leanh::lean_dec(v___x_5351_);
                            v___x_5369_ = leanh::lean_box(0);
                            v_isShared_5370_ = v_isSharedCheck_5374_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5375_ = leanh::lean_ctor_get(v_n_5341_, 0);
                    v___x_5376_ = leanh::lean_box(0);
                    v___x_5377_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5377_, 0, v___x_5376_);
                    leanh::lean_ctor_set(v___x_5377_, 1, v_b_5342_);
                    v_sz_5378_ = lean_array_size(v_vs_5375_);
                    v___x_5379_ = 0usize;
                    v___x_5380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_5340_, v_vs_5375_, v_sz_5378_, v___x_5379_, v___x_5377_, v___y_5343_, v___y_5344_);
                    if leanh::lean_obj_tag(v___x_5380_) == 0 {
                        v_a_5381_ = leanh::lean_ctor_get(v___x_5380_, 0);
                        v_isSharedCheck_5395_ =
                            (!leanh::lean_is_exclusive(v___x_5380_)) as u8;
                        if v_isSharedCheck_5395_ == 0 {
                            v___x_5383_ = v___x_5380_;
                            v_isShared_5384_ = v_isSharedCheck_5395_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5381_);
                            leanh::lean_dec(v___x_5380_);
                            v___x_5383_ = leanh::lean_box(0);
                            v_isShared_5384_ = v_isSharedCheck_5395_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5396_ = leanh::lean_ctor_get(v___x_5380_, 0);
                        v_isSharedCheck_5403_ =
                            (!leanh::lean_is_exclusive(v___x_5380_)) as u8;
                        if v_isSharedCheck_5403_ == 0 {
                            v___x_5398_ = v___x_5380_;
                            v_isShared_5399_ = v_isSharedCheck_5403_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5396_);
                            leanh::lean_dec(v___x_5380_);
                            v___x_5398_ = leanh::lean_box(0);
                            v_isShared_5399_ = v_isSharedCheck_5403_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5356_ = leanh::lean_ctor_get(v_a_5352_, 0);
                if leanh::lean_obj_tag(v_fst_5356_) == 0 {
                    v_snd_5357_ = leanh::lean_ctor_get(v_a_5352_, 1);
                    leanh::lean_inc(v_snd_5357_);
                    leanh::lean_dec(v_a_5352_);
                    v___x_5358_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5358_, 0, v_snd_5357_);
                    if v_isShared_5355_ == 0 {
                        leanh::lean_ctor_set(v___x_5354_, 0, v___x_5358_);
                        v___x_5360_ = v___x_5354_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5361_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5361_, 0, v___x_5358_);
                        v___x_5360_ = v_reuseFailAlloc_5361_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5356_);
                    leanh::lean_dec(v_a_5352_);
                    v_val_5362_ = leanh::lean_ctor_get(v_fst_5356_, 0);
                    leanh::lean_inc(v_val_5362_);
                    leanh::lean_dec_ref_known(v_fst_5356_, 1);
                    if v_isShared_5355_ == 0 {
                        leanh::lean_ctor_set(v___x_5354_, 0, v_val_5362_);
                        v___x_5364_ = v___x_5354_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_val_5362_);
                        v___x_5364_ = v_reuseFailAlloc_5365_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5360_;
            }
            3 => {
                return v___x_5364_;
            }
            4 => {
                if v_isShared_5370_ == 0 {
                    v___x_5372_ = v___x_5369_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
                    v___x_5372_ = v_reuseFailAlloc_5373_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5372_;
            }
            6 => {
                v_fst_5385_ = leanh::lean_ctor_get(v_a_5381_, 0);
                if leanh::lean_obj_tag(v_fst_5385_) == 0 {
                    v_snd_5386_ = leanh::lean_ctor_get(v_a_5381_, 1);
                    leanh::lean_inc(v_snd_5386_);
                    leanh::lean_dec(v_a_5381_);
                    v___x_5387_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5387_, 0, v_snd_5386_);
                    if v_isShared_5384_ == 0 {
                        leanh::lean_ctor_set(v___x_5383_, 0, v___x_5387_);
                        v___x_5389_ = v___x_5383_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5387_);
                        v___x_5389_ = v_reuseFailAlloc_5390_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5385_);
                    leanh::lean_dec(v_a_5381_);
                    v_val_5391_ = leanh::lean_ctor_get(v_fst_5385_, 0);
                    leanh::lean_inc(v_val_5391_);
                    leanh::lean_dec_ref_known(v_fst_5385_, 1);
                    if v_isShared_5384_ == 0 {
                        leanh::lean_ctor_set(v___x_5383_, 0, v_val_5391_);
                        v___x_5393_ = v___x_5383_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5394_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_val_5391_);
                        v___x_5393_ = v_reuseFailAlloc_5394_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5389_;
            }
            8 => {
                return v___x_5393_;
            }
            9 => {
                if v_isShared_5399_ == 0 {
                    v___x_5401_ = v___x_5398_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5402_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
                    v___x_5401_ = v_reuseFailAlloc_5402_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(
    mut v_init_5404_: *mut leanh::LeanObject,
    mut v___x_5405_: u8,
    mut v_as_5406_: *mut leanh::LeanObject,
    mut v_sz_5407_: usize,
    mut v_i_5408_: usize,
    mut v_b_5409_: *mut leanh::LeanObject,
    mut v___y_5410_: *mut leanh::LeanObject,
    mut v___y_5411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5413_: u8 = 0;
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5418_: u8 = 0;
    let mut v_a_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: usize = 0;
    let mut v___x_5437_: usize = 0;
    let mut v_reuseFailAlloc_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5440_: u8 = 0;
    let mut v_a_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5444_: u8 = 0;
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5448_: u8 = 0;
    let mut v_isSharedCheck_5449_: u8 = 0;
    let mut v_unused_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5413_ = lean_usize_dec_lt(v_i_5408_, v_sz_5407_);
                if v___x_5413_ == 0 {
                    v___x_5414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5414_, 0, v_b_5409_);
                    return v___x_5414_;
                } else {
                    v_snd_5415_ = leanh::lean_ctor_get(v_b_5409_, 1);
                    v_isSharedCheck_5449_ = (!leanh::lean_is_exclusive(v_b_5409_)) as u8;
                    if v_isSharedCheck_5449_ == 0 {
                        v_unused_5450_ = leanh::lean_ctor_get(v_b_5409_, 0);
                        leanh::lean_dec(v_unused_5450_);
                        v___x_5417_ = v_b_5409_;
                        v_isShared_5418_ = v_isSharedCheck_5449_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5415_);
                        leanh::lean_dec(v_b_5409_);
                        v___x_5417_ = leanh::lean_box(0);
                        v_isShared_5418_ = v_isSharedCheck_5449_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5419_ = lean_array_uget_borrowed(v_as_5406_, v_i_5408_);
                leanh::lean_inc(v_snd_5415_);
                v___x_5420_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_5404_, v___x_5405_, v_a_5419_, v_snd_5415_, v___y_5410_, v___y_5411_);
                if leanh::lean_obj_tag(v___x_5420_) == 0 {
                    v_a_5421_ = leanh::lean_ctor_get(v___x_5420_, 0);
                    v_isSharedCheck_5440_ = (!leanh::lean_is_exclusive(v___x_5420_)) as u8;
                    if v_isSharedCheck_5440_ == 0 {
                        v___x_5423_ = v___x_5420_;
                        v_isShared_5424_ = v_isSharedCheck_5440_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5421_);
                        leanh::lean_dec(v___x_5420_);
                        v___x_5423_ = leanh::lean_box(0);
                        v_isShared_5424_ = v_isSharedCheck_5440_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5417_);
                    leanh::lean_dec(v_snd_5415_);
                    v_a_5441_ = leanh::lean_ctor_get(v___x_5420_, 0);
                    v_isSharedCheck_5448_ = (!leanh::lean_is_exclusive(v___x_5420_)) as u8;
                    if v_isSharedCheck_5448_ == 0 {
                        v___x_5443_ = v___x_5420_;
                        v_isShared_5444_ = v_isSharedCheck_5448_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5441_);
                        leanh::lean_dec(v___x_5420_);
                        v___x_5443_ = leanh::lean_box(0);
                        v_isShared_5444_ = v_isSharedCheck_5448_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5421_) == 0 {
                    v___x_5425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5425_, 0, v_a_5421_);
                    if v_isShared_5418_ == 0 {
                        leanh::lean_ctor_set(v___x_5417_, 0, v___x_5425_);
                        v___x_5427_ = v___x_5417_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5425_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5431_, 1, v_snd_5415_);
                        v___x_5427_ = v_reuseFailAlloc_5431_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5423_);
                    leanh::lean_dec(v_snd_5415_);
                    v_a_5432_ = leanh::lean_ctor_get(v_a_5421_, 0);
                    leanh::lean_inc(v_a_5432_);
                    leanh::lean_dec_ref_known(v_a_5421_, 1);
                    v___x_5433_ = leanh::lean_box(0);
                    if v_isShared_5418_ == 0 {
                        leanh::lean_ctor_set(v___x_5417_, 1, v_a_5432_);
                        leanh::lean_ctor_set(v___x_5417_, 0, v___x_5433_);
                        v___x_5435_ = v___x_5417_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5439_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 0, v___x_5433_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 1, v_a_5432_);
                        v___x_5435_ = v_reuseFailAlloc_5439_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5424_ == 0 {
                    leanh::lean_ctor_set(v___x_5423_, 0, v___x_5427_);
                    v___x_5429_ = v___x_5423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5430_, 0, v___x_5427_);
                    v___x_5429_ = v_reuseFailAlloc_5430_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5429_;
            }
            5 => {
                v___x_5436_ = 1usize;
                v___x_5437_ = lean_usize_add(v_i_5408_, v___x_5436_);
                v_i_5408_ = v___x_5437_;
                v_b_5409_ = v___x_5435_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5444_ == 0 {
                    v___x_5446_ = v___x_5443_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5447_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_a_5441_);
                    v___x_5446_ = v_reuseFailAlloc_5447_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(
    mut v_init_5451_: *mut leanh::LeanObject,
    mut v___x_5452_: *mut leanh::LeanObject,
    mut v_as_5453_: *mut leanh::LeanObject,
    mut v_sz_5454_: *mut leanh::LeanObject,
    mut v_i_5455_: *mut leanh::LeanObject,
    mut v_b_5456_: *mut leanh::LeanObject,
    mut v___y_5457_: *mut leanh::LeanObject,
    mut v___y_5458_: *mut leanh::LeanObject,
    mut v___y_5459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37918__boxed_5460_: u8 = 0;
    let mut v_sz_boxed_5461_: usize = 0;
    let mut v_i_boxed_5462_: usize = 0;
    let mut v_res_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37918__boxed_5460_ = (leanh::lean_unbox(v___x_5452_) as u8);
    v_sz_boxed_5461_ = leanh::lean_unbox_usize(v_sz_5454_);
    leanh::lean_dec(v_sz_5454_);
    v_i_boxed_5462_ = leanh::lean_unbox_usize(v_i_5455_);
    leanh::lean_dec(v_i_5455_);
    v_res_5463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_5451_, v___x_37918__boxed_5460_, v_as_5453_, v_sz_boxed_5461_, v_i_boxed_5462_, v_b_5456_, v___y_5457_, v___y_5458_);
    leanh::lean_dec(v___y_5458_);
    leanh::lean_dec_ref(v___y_5457_);
    leanh::lean_dec_ref(v_as_5453_);
    leanh::lean_dec_ref(v_init_5451_);
    return v_res_5463_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(
    mut v_init_5464_: *mut leanh::LeanObject,
    mut v___x_5465_: *mut leanh::LeanObject,
    mut v_n_5466_: *mut leanh::LeanObject,
    mut v_b_5467_: *mut leanh::LeanObject,
    mut v___y_5468_: *mut leanh::LeanObject,
    mut v___y_5469_: *mut leanh::LeanObject,
    mut v___y_5470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37938__boxed_5471_: u8 = 0;
    let mut v_res_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37938__boxed_5471_ = (leanh::lean_unbox(v___x_5465_) as u8);
    v_res_5472_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_5464_, v___x_37938__boxed_5471_, v_n_5466_, v_b_5467_, v___y_5468_, v___y_5469_);
    leanh::lean_dec(v___y_5469_);
    leanh::lean_dec_ref(v___y_5468_);
    leanh::lean_dec_ref(v_n_5466_);
    leanh::lean_dec_ref(v_init_5464_);
    return v_res_5472_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(
    mut v___x_5473_: u8,
    mut v_as_5474_: *mut leanh::LeanObject,
    mut v_sz_5475_: usize,
    mut v_i_5476_: usize,
    mut v_b_5477_: *mut leanh::LeanObject,
    mut v___y_5478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5480_: u8 = 0;
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5485_: u8 = 0;
    let mut v_ref_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5492_: u8 = 0;
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: usize = 0;
    let mut v___x_5506_: usize = 0;
    let mut v_reuseFailAlloc_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5518_: u8 = 0;
    let mut v_isSharedCheck_5519_: u8 = 0;
    let mut v_unused_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5480_ = lean_usize_dec_lt(v_i_5476_, v_sz_5475_);
                if v___x_5480_ == 0 {
                    v___x_5481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5481_, 0, v_b_5477_);
                    return v___x_5481_;
                } else {
                    v_snd_5482_ = leanh::lean_ctor_get(v_b_5477_, 1);
                    v_isSharedCheck_5519_ = (!leanh::lean_is_exclusive(v_b_5477_)) as u8;
                    if v_isSharedCheck_5519_ == 0 {
                        v_unused_5520_ = leanh::lean_ctor_get(v_b_5477_, 0);
                        leanh::lean_dec(v_unused_5520_);
                        v___x_5484_ = v_b_5477_;
                        v_isShared_5485_ = v_isSharedCheck_5519_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5482_);
                        leanh::lean_dec(v_b_5477_);
                        v___x_5484_ = leanh::lean_box(0);
                        v_isShared_5485_ = v_isSharedCheck_5519_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_5486_ = leanh::lean_ctor_get(v___y_5478_, 5);
                v_a_5487_ = lean_array_uget(v_as_5474_, v_i_5476_);
                v_ref_5488_ = leanh::lean_ctor_get(v_a_5487_, 0);
                v_msg_5489_ = leanh::lean_ctor_get(v_a_5487_, 1);
                v_isSharedCheck_5518_ = (!leanh::lean_is_exclusive(v_a_5487_)) as u8;
                if v_isSharedCheck_5518_ == 0 {
                    v___x_5491_ = v_a_5487_;
                    v_isShared_5492_ = v_isSharedCheck_5518_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_msg_5489_);
                    leanh::lean_inc(v_ref_5488_);
                    leanh::lean_dec(v_a_5487_);
                    v___x_5491_ = leanh::lean_box(0);
                    v_isShared_5492_ = v_isSharedCheck_5518_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5493_ = leanh::lean_box(0);
                v_ref_5510_ = l_Lean_replaceRef(v_ref_5488_, v_ref_5486_);
                leanh::lean_dec(v_ref_5488_);
                v___x_5515_ = l_Lean_Syntax_getPos_x3f(v_ref_5510_, v___x_5473_);
                if leanh::lean_obj_tag(v___x_5515_) == 0 {
                    v___x_5516_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5512_ = v___x_5516_;
                    state = 6;
                    continue;
                } else {
                    v_val_5517_ = leanh::lean_ctor_get(v___x_5515_, 0);
                    leanh::lean_inc(v_val_5517_);
                    leanh::lean_dec_ref_known(v___x_5515_, 1);
                    v___y_5512_ = v_val_5517_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                if v_isShared_5485_ == 0 {
                    leanh::lean_ctor_set(v___x_5484_, 1, v___y_5496_);
                    leanh::lean_ctor_set(v___x_5484_, 0, v___y_5495_);
                    v___x_5498_ = v___x_5484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5509_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5509_, 0, v___y_5495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5509_, 1, v___y_5496_);
                    v___x_5498_ = v_reuseFailAlloc_5509_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0;
                v___x_5500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_5482_, v___x_5498_, v___x_5499_);
                v___x_5501_ = lean_array_push(v___x_5500_, v_msg_5489_);
                v_pos2traces_5502_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_5482_, v___x_5498_, v___x_5501_);
                if v_isShared_5492_ == 0 {
                    leanh::lean_ctor_set(v___x_5491_, 1, v_pos2traces_5502_);
                    leanh::lean_ctor_set(v___x_5491_, 0, v___x_5493_);
                    v___x_5504_ = v___x_5491_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5508_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5508_, 0, v___x_5493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5508_, 1, v_pos2traces_5502_);
                    v___x_5504_ = v_reuseFailAlloc_5508_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5505_ = 1usize;
                v___x_5506_ = lean_usize_add(v_i_5476_, v___x_5505_);
                v_i_5476_ = v___x_5506_;
                v_b_5477_ = v___x_5504_;
                state = 0;
                continue;
            }
            6 => {
                v___x_5513_ = l_Lean_Syntax_getTailPos_x3f(v_ref_5510_, v___x_5473_);
                leanh::lean_dec(v_ref_5510_);
                if leanh::lean_obj_tag(v___x_5513_) == 0 {
                    leanh::lean_inc(v___y_5512_);
                    v___y_5495_ = v___y_5512_;
                    v___y_5496_ = v___y_5512_;
                    state = 3;
                    continue;
                } else {
                    v_val_5514_ = leanh::lean_ctor_get(v___x_5513_, 0);
                    leanh::lean_inc(v_val_5514_);
                    leanh::lean_dec_ref_known(v___x_5513_, 1);
                    v___y_5495_ = v___y_5512_;
                    v___y_5496_ = v_val_5514_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(
    mut v___x_5521_: *mut leanh::LeanObject,
    mut v_as_5522_: *mut leanh::LeanObject,
    mut v_sz_5523_: *mut leanh::LeanObject,
    mut v_i_5524_: *mut leanh::LeanObject,
    mut v_b_5525_: *mut leanh::LeanObject,
    mut v___y_5526_: *mut leanh::LeanObject,
    mut v___y_5527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_38121__boxed_5528_: u8 = 0;
    let mut v_sz_boxed_5529_: usize = 0;
    let mut v_i_boxed_5530_: usize = 0;
    let mut v_res_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_38121__boxed_5528_ = (leanh::lean_unbox(v___x_5521_) as u8);
    v_sz_boxed_5529_ = leanh::lean_unbox_usize(v_sz_5523_);
    leanh::lean_dec(v_sz_5523_);
    v_i_boxed_5530_ = leanh::lean_unbox_usize(v_i_5524_);
    leanh::lean_dec(v_i_5524_);
    v_res_5531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38121__boxed_5528_, v_as_5522_, v_sz_boxed_5529_, v_i_boxed_5530_, v_b_5525_, v___y_5526_);
    leanh::lean_dec_ref(v___y_5526_);
    leanh::lean_dec_ref(v_as_5522_);
    return v_res_5531_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(
    mut v___x_5532_: u8,
    mut v_as_5533_: *mut leanh::LeanObject,
    mut v_sz_5534_: usize,
    mut v_i_5535_: usize,
    mut v_b_5536_: *mut leanh::LeanObject,
    mut v___y_5537_: *mut leanh::LeanObject,
    mut v___y_5538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5540_: u8 = 0;
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5545_: u8 = 0;
    let mut v_ref_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5552_: u8 = 0;
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: usize = 0;
    let mut v___x_5566_: usize = 0;
    let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_unused_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5540_ = lean_usize_dec_lt(v_i_5535_, v_sz_5534_);
                if v___x_5540_ == 0 {
                    v___x_5541_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5541_, 0, v_b_5536_);
                    return v___x_5541_;
                } else {
                    v_snd_5542_ = leanh::lean_ctor_get(v_b_5536_, 1);
                    v_isSharedCheck_5579_ = (!leanh::lean_is_exclusive(v_b_5536_)) as u8;
                    if v_isSharedCheck_5579_ == 0 {
                        v_unused_5580_ = leanh::lean_ctor_get(v_b_5536_, 0);
                        leanh::lean_dec(v_unused_5580_);
                        v___x_5544_ = v_b_5536_;
                        v_isShared_5545_ = v_isSharedCheck_5579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5542_);
                        leanh::lean_dec(v_b_5536_);
                        v___x_5544_ = leanh::lean_box(0);
                        v_isShared_5545_ = v_isSharedCheck_5579_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_5546_ = leanh::lean_ctor_get(v___y_5537_, 5);
                v_a_5547_ = lean_array_uget(v_as_5533_, v_i_5535_);
                v_ref_5548_ = leanh::lean_ctor_get(v_a_5547_, 0);
                v_msg_5549_ = leanh::lean_ctor_get(v_a_5547_, 1);
                v_isSharedCheck_5578_ = (!leanh::lean_is_exclusive(v_a_5547_)) as u8;
                if v_isSharedCheck_5578_ == 0 {
                    v___x_5551_ = v_a_5547_;
                    v_isShared_5552_ = v_isSharedCheck_5578_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_msg_5549_);
                    leanh::lean_inc(v_ref_5548_);
                    leanh::lean_dec(v_a_5547_);
                    v___x_5551_ = leanh::lean_box(0);
                    v_isShared_5552_ = v_isSharedCheck_5578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5553_ = leanh::lean_box(0);
                v_ref_5570_ = l_Lean_replaceRef(v_ref_5548_, v_ref_5546_);
                leanh::lean_dec(v_ref_5548_);
                v___x_5575_ = l_Lean_Syntax_getPos_x3f(v_ref_5570_, v___x_5532_);
                if leanh::lean_obj_tag(v___x_5575_) == 0 {
                    v___x_5576_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5572_ = v___x_5576_;
                    state = 6;
                    continue;
                } else {
                    v_val_5577_ = leanh::lean_ctor_get(v___x_5575_, 0);
                    leanh::lean_inc(v_val_5577_);
                    leanh::lean_dec_ref_known(v___x_5575_, 1);
                    v___y_5572_ = v_val_5577_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                if v_isShared_5545_ == 0 {
                    leanh::lean_ctor_set(v___x_5544_, 1, v___y_5556_);
                    leanh::lean_ctor_set(v___x_5544_, 0, v___y_5555_);
                    v___x_5558_ = v___x_5544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5569_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___y_5555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 1, v___y_5556_);
                    v___x_5558_ = v_reuseFailAlloc_5569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0;
                v___x_5560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_5542_, v___x_5558_, v___x_5559_);
                v___x_5561_ = lean_array_push(v___x_5560_, v_msg_5549_);
                v_pos2traces_5562_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_5542_, v___x_5558_, v___x_5561_);
                if v_isShared_5552_ == 0 {
                    leanh::lean_ctor_set(v___x_5551_, 1, v_pos2traces_5562_);
                    leanh::lean_ctor_set(v___x_5551_, 0, v___x_5553_);
                    v___x_5564_ = v___x_5551_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5568_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_pos2traces_5562_);
                    v___x_5564_ = v_reuseFailAlloc_5568_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5565_ = 1usize;
                v___x_5566_ = lean_usize_add(v_i_5535_, v___x_5565_);
                v___x_5567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_5532_, v_as_5533_, v_sz_5534_, v___x_5566_, v___x_5564_, v___y_5537_);
                return v___x_5567_;
            }
            6 => {
                v___x_5573_ = l_Lean_Syntax_getTailPos_x3f(v_ref_5570_, v___x_5532_);
                leanh::lean_dec(v_ref_5570_);
                if leanh::lean_obj_tag(v___x_5573_) == 0 {
                    leanh::lean_inc(v___y_5572_);
                    v___y_5555_ = v___y_5572_;
                    v___y_5556_ = v___y_5572_;
                    state = 3;
                    continue;
                } else {
                    v_val_5574_ = leanh::lean_ctor_get(v___x_5573_, 0);
                    leanh::lean_inc(v_val_5574_);
                    leanh::lean_dec_ref_known(v___x_5573_, 1);
                    v___y_5555_ = v___y_5572_;
                    v___y_5556_ = v_val_5574_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(
    mut v___x_5581_: *mut leanh::LeanObject,
    mut v_as_5582_: *mut leanh::LeanObject,
    mut v_sz_5583_: *mut leanh::LeanObject,
    mut v_i_5584_: *mut leanh::LeanObject,
    mut v_b_5585_: *mut leanh::LeanObject,
    mut v___y_5586_: *mut leanh::LeanObject,
    mut v___y_5587_: *mut leanh::LeanObject,
    mut v___y_5588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_38201__boxed_5589_: u8 = 0;
    let mut v_sz_boxed_5590_: usize = 0;
    let mut v_i_boxed_5591_: usize = 0;
    let mut v_res_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_38201__boxed_5589_ = (leanh::lean_unbox(v___x_5581_) as u8);
    v_sz_boxed_5590_ = leanh::lean_unbox_usize(v_sz_5583_);
    leanh::lean_dec(v_sz_5583_);
    v_i_boxed_5591_ = leanh::lean_unbox_usize(v_i_5584_);
    leanh::lean_dec(v_i_5584_);
    v_res_5592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38201__boxed_5589_, v_as_5582_, v_sz_boxed_5590_, v_i_boxed_5591_, v_b_5585_, v___y_5586_, v___y_5587_);
    leanh::lean_dec(v___y_5587_);
    leanh::lean_dec_ref(v___y_5586_);
    leanh::lean_dec_ref(v_as_5582_);
    return v_res_5592_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(
    mut v___x_5593_: u8,
    mut v_t_5594_: *mut leanh::LeanObject,
    mut v_init_5595_: *mut leanh::LeanObject,
    mut v___y_5596_: *mut leanh::LeanObject,
    mut v___y_5597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v_a_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5613_: usize = 0;
    let mut v___x_5614_: usize = 0;
    let mut v___x_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5619_: u8 = 0;
    let mut v_fst_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5629_: u8 = 0;
    let mut v_a_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5633_: u8 = 0;
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5637_: u8 = 0;
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut v_a_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5599_ = leanh::lean_ctor_get(v_t_5594_, 0);
                v_tail_5600_ = leanh::lean_ctor_get(v_t_5594_, 1);
                leanh::lean_inc_ref(v_init_5595_);
                v___x_5601_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_5595_, v___x_5593_, v_root_5599_, v_init_5595_, v___y_5596_, v___y_5597_);
                leanh::lean_dec_ref(v_init_5595_);
                if leanh::lean_obj_tag(v___x_5601_) == 0 {
                    v_a_5602_ = leanh::lean_ctor_get(v___x_5601_, 0);
                    v_isSharedCheck_5638_ = (!leanh::lean_is_exclusive(v___x_5601_)) as u8;
                    if v_isSharedCheck_5638_ == 0 {
                        v___x_5604_ = v___x_5601_;
                        v_isShared_5605_ = v_isSharedCheck_5638_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5602_);
                        leanh::lean_dec(v___x_5601_);
                        v___x_5604_ = leanh::lean_box(0);
                        v_isShared_5605_ = v_isSharedCheck_5638_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5639_ = leanh::lean_ctor_get(v___x_5601_, 0);
                    v_isSharedCheck_5646_ = (!leanh::lean_is_exclusive(v___x_5601_)) as u8;
                    if v_isSharedCheck_5646_ == 0 {
                        v___x_5641_ = v___x_5601_;
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5639_);
                        leanh::lean_dec(v___x_5601_);
                        v___x_5641_ = leanh::lean_box(0);
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5602_) == 0 {
                    v_a_5606_ = leanh::lean_ctor_get(v_a_5602_, 0);
                    leanh::lean_inc(v_a_5606_);
                    leanh::lean_dec_ref_known(v_a_5602_, 1);
                    if v_isShared_5605_ == 0 {
                        leanh::lean_ctor_set(v___x_5604_, 0, v_a_5606_);
                        v___x_5608_ = v___x_5604_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5606_);
                        v___x_5608_ = v_reuseFailAlloc_5609_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5604_);
                    v_a_5610_ = leanh::lean_ctor_get(v_a_5602_, 0);
                    leanh::lean_inc(v_a_5610_);
                    leanh::lean_dec_ref_known(v_a_5602_, 1);
                    v___x_5611_ = leanh::lean_box(0);
                    v___x_5612_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5612_, 0, v___x_5611_);
                    leanh::lean_ctor_set(v___x_5612_, 1, v_a_5610_);
                    v_sz_5613_ = lean_array_size(v_tail_5600_);
                    v___x_5614_ = 0usize;
                    v___x_5615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_5593_, v_tail_5600_, v_sz_5613_, v___x_5614_, v___x_5612_, v___y_5596_, v___y_5597_);
                    if leanh::lean_obj_tag(v___x_5615_) == 0 {
                        v_a_5616_ = leanh::lean_ctor_get(v___x_5615_, 0);
                        v_isSharedCheck_5629_ =
                            (!leanh::lean_is_exclusive(v___x_5615_)) as u8;
                        if v_isSharedCheck_5629_ == 0 {
                            v___x_5618_ = v___x_5615_;
                            v_isShared_5619_ = v_isSharedCheck_5629_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5616_);
                            leanh::lean_dec(v___x_5615_);
                            v___x_5618_ = leanh::lean_box(0);
                            v_isShared_5619_ = v_isSharedCheck_5629_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5630_ = leanh::lean_ctor_get(v___x_5615_, 0);
                        v_isSharedCheck_5637_ =
                            (!leanh::lean_is_exclusive(v___x_5615_)) as u8;
                        if v_isSharedCheck_5637_ == 0 {
                            v___x_5632_ = v___x_5615_;
                            v_isShared_5633_ = v_isSharedCheck_5637_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5630_);
                            leanh::lean_dec(v___x_5615_);
                            v___x_5632_ = leanh::lean_box(0);
                            v_isShared_5633_ = v_isSharedCheck_5637_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5608_;
            }
            3 => {
                v_fst_5620_ = leanh::lean_ctor_get(v_a_5616_, 0);
                if leanh::lean_obj_tag(v_fst_5620_) == 0 {
                    v_snd_5621_ = leanh::lean_ctor_get(v_a_5616_, 1);
                    leanh::lean_inc(v_snd_5621_);
                    leanh::lean_dec(v_a_5616_);
                    if v_isShared_5619_ == 0 {
                        leanh::lean_ctor_set(v___x_5618_, 0, v_snd_5621_);
                        v___x_5623_ = v___x_5618_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_snd_5621_);
                        v___x_5623_ = v_reuseFailAlloc_5624_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5620_);
                    leanh::lean_dec(v_a_5616_);
                    v_val_5625_ = leanh::lean_ctor_get(v_fst_5620_, 0);
                    leanh::lean_inc(v_val_5625_);
                    leanh::lean_dec_ref_known(v_fst_5620_, 1);
                    if v_isShared_5619_ == 0 {
                        leanh::lean_ctor_set(v___x_5618_, 0, v_val_5625_);
                        v___x_5627_ = v___x_5618_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5628_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_val_5625_);
                        v___x_5627_ = v_reuseFailAlloc_5628_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5623_;
            }
            5 => {
                return v___x_5627_;
            }
            6 => {
                if v_isShared_5633_ == 0 {
                    v___x_5635_ = v___x_5632_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5636_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_a_5630_);
                    v___x_5635_ = v_reuseFailAlloc_5636_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5635_;
            }
            8 => {
                if v_isShared_5642_ == 0 {
                    v___x_5644_ = v___x_5641_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
                    v___x_5644_ = v_reuseFailAlloc_5645_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(
    mut v___x_5647_: *mut leanh::LeanObject,
    mut v_t_5648_: *mut leanh::LeanObject,
    mut v_init_5649_: *mut leanh::LeanObject,
    mut v___y_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_38282__boxed_5653_: u8 = 0;
    let mut v_res_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_38282__boxed_5653_ = (leanh::lean_unbox(v___x_5647_) as u8);
    v_res_5654_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38282__boxed_5653_, v_t_5648_, v_init_5649_, v___y_5650_, v___y_5651_);
    leanh::lean_dec(v___y_5651_);
    leanh::lean_dec_ref(v___y_5650_);
    leanh::lean_dec_ref(v_t_5648_);
    return v_res_5654_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(
    mut v_x_5655_: *mut leanh::LeanObject,
    mut v_x_5656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5656_) == 0 {
                    return v_x_5655_;
                } else {
                    v_key_5657_ = leanh::lean_ctor_get(v_x_5656_, 0);
                    v_value_5658_ = leanh::lean_ctor_get(v_x_5656_, 1);
                    v_tail_5659_ = leanh::lean_ctor_get(v_x_5656_, 2);
                    leanh::lean_inc(v_value_5658_);
                    leanh::lean_inc(v_key_5657_);
                    v___x_5660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5660_, 0, v_key_5657_);
                    leanh::lean_ctor_set(v___x_5660_, 1, v_value_5658_);
                    v___x_5661_ = lean_array_push(v_x_5655_, v___x_5660_);
                    v_x_5655_ = v___x_5661_;
                    v_x_5656_ = v_tail_5659_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(
    mut v_x_5663_: *mut leanh::LeanObject,
    mut v_x_5664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5665_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_5663_, v_x_5664_);
    leanh::lean_dec(v_x_5664_);
    return v_res_5665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(
    mut v_as_5666_: *mut leanh::LeanObject,
    mut v_i_5667_: usize,
    mut v_stop_5668_: usize,
    mut v_b_5669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5670_: u8 = 0;
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: usize = 0;
    let mut v___x_5674_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5670_ = lean_usize_dec_eq(v_i_5667_, v_stop_5668_);
                if v___x_5670_ == 0 {
                    v___x_5671_ = lean_array_uget_borrowed(v_as_5666_, v_i_5667_);
                    v___x_5672_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_5669_, v___x_5671_);
                    v___x_5673_ = 1usize;
                    v___x_5674_ = lean_usize_add(v_i_5667_, v___x_5673_);
                    v_i_5667_ = v___x_5674_;
                    v_b_5669_ = v___x_5672_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(
    mut v_as_5676_: *mut leanh::LeanObject,
    mut v_i_5677_: *mut leanh::LeanObject,
    mut v_stop_5678_: *mut leanh::LeanObject,
    mut v_b_5679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5680_: usize = 0;
    let mut v_stop_boxed_5681_: usize = 0;
    let mut v_res_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5680_ = leanh::lean_unbox_usize(v_i_5677_);
    leanh::lean_dec(v_i_5677_);
    v_stop_boxed_5681_ = leanh::lean_unbox_usize(v_stop_5678_);
    leanh::lean_dec(v_stop_5678_);
    v_res_5682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_5676_, v_i_boxed_5680_, v_stop_boxed_5681_, v_b_5679_);
    leanh::lean_dec_ref(v_as_5676_);
    return v_res_5682_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5683_ = leanh::lean_unsigned_to_nat(32);
    v___x_5684_ = lean_mk_empty_array_with_capacity(v___x_5683_);
    v___x_5685_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5685_, 0, v___x_5684_);
    return v___x_5685_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5686_: usize = 0;
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5686_ = 5usize;
    v___x_5687_ = leanh::lean_unsigned_to_nat(0);
    v___x_5688_ = leanh::lean_unsigned_to_nat(32);
    v___x_5689_ = lean_mk_empty_array_with_capacity(v___x_5688_);
    v___x_5690_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
    v___x_5691_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5691_, 0, v___x_5690_);
    leanh::lean_ctor_set(v___x_5691_, 1, v___x_5689_);
    leanh::lean_ctor_set(v___x_5691_, 2, v___x_5687_);
    leanh::lean_ctor_set(v___x_5691_, 3, v___x_5687_);
    leanh::lean_ctor_set_usize(v___x_5691_, 4, v___x_5686_);
    return v___x_5691_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(
    mut v___y_5692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5709_: u8 = 0;
    let mut v_tid_5710_: u64 = 0;
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5713_: u8 = 0;
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5723_: u8 = 0;
    let mut v_unused_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5694_ = lean_st_ref_get(v___y_5692_);
                v_traceState_5695_ = leanh::lean_ctor_get(v___x_5694_, 4);
                leanh::lean_inc_ref(v_traceState_5695_);
                leanh::lean_dec(v___x_5694_);
                v_traces_5696_ = leanh::lean_ctor_get(v_traceState_5695_, 0);
                leanh::lean_inc_ref(v_traces_5696_);
                leanh::lean_dec_ref(v_traceState_5695_);
                v___x_5697_ = lean_st_ref_take(v___y_5692_);
                v_traceState_5698_ = leanh::lean_ctor_get(v___x_5697_, 4);
                v_env_5699_ = leanh::lean_ctor_get(v___x_5697_, 0);
                v_nextMacroScope_5700_ = leanh::lean_ctor_get(v___x_5697_, 1);
                v_ngen_5701_ = leanh::lean_ctor_get(v___x_5697_, 2);
                v_auxDeclNGen_5702_ = leanh::lean_ctor_get(v___x_5697_, 3);
                v_cache_5703_ = leanh::lean_ctor_get(v___x_5697_, 5);
                v_messages_5704_ = leanh::lean_ctor_get(v___x_5697_, 6);
                v_infoState_5705_ = leanh::lean_ctor_get(v___x_5697_, 7);
                v_snapshotTasks_5706_ = leanh::lean_ctor_get(v___x_5697_, 8);
                v_isSharedCheck_5725_ = (!leanh::lean_is_exclusive(v___x_5697_)) as u8;
                if v_isSharedCheck_5725_ == 0 {
                    v___x_5708_ = v___x_5697_;
                    v_isShared_5709_ = v_isSharedCheck_5725_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5706_);
                    leanh::lean_inc(v_infoState_5705_);
                    leanh::lean_inc(v_messages_5704_);
                    leanh::lean_inc(v_cache_5703_);
                    leanh::lean_inc(v_traceState_5698_);
                    leanh::lean_inc(v_auxDeclNGen_5702_);
                    leanh::lean_inc(v_ngen_5701_);
                    leanh::lean_inc(v_nextMacroScope_5700_);
                    leanh::lean_inc(v_env_5699_);
                    leanh::lean_dec(v___x_5697_);
                    v___x_5708_ = leanh::lean_box(0);
                    v_isShared_5709_ = v_isSharedCheck_5725_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_5710_ = leanh::lean_ctor_get_uint64(
                    v_traceState_5698_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5723_ =
                    (!leanh::lean_is_exclusive(v_traceState_5698_)) as u8;
                if v_isSharedCheck_5723_ == 0 {
                    v_unused_5724_ = leanh::lean_ctor_get(v_traceState_5698_, 0);
                    leanh::lean_dec(v_unused_5724_);
                    v___x_5712_ = v_traceState_5698_;
                    v_isShared_5713_ = v_isSharedCheck_5723_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_5698_);
                    v___x_5712_ = leanh::lean_box(0);
                    v_isShared_5713_ = v_isSharedCheck_5723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5714_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
                if v_isShared_5713_ == 0 {
                    leanh::lean_ctor_set(v___x_5712_, 0, v___x_5714_);
                    v___x_5716_ = v___x_5712_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5722_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5722_, 0, v___x_5714_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5722_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_5710_,
                    );
                    v___x_5716_ = v_reuseFailAlloc_5722_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5709_ == 0 {
                    leanh::lean_ctor_set(v___x_5708_, 4, v___x_5716_);
                    v___x_5718_ = v___x_5708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5721_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_env_5699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 1, v_nextMacroScope_5700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 2, v_ngen_5701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 3, v_auxDeclNGen_5702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 4, v___x_5716_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 5, v_cache_5703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 6, v_messages_5704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 7, v_infoState_5705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 8, v_snapshotTasks_5706_);
                    v___x_5718_ = v_reuseFailAlloc_5721_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5719_ = lean_st_ref_set(v___y_5692_, v___x_5718_);
                v___x_5720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5720_, 0, v_traces_5696_);
                return v___x_5720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(
    mut v___y_5726_: *mut leanh::LeanObject,
    mut v___y_5727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5728_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_5726_);
    leanh::lean_dec(v___y_5726_);
    return v_res_5728_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(
    mut v_hi_5729_: *mut leanh::LeanObject,
    mut v_pivot_5730_: *mut leanh::LeanObject,
    mut v_as_5731_: *mut leanh::LeanObject,
    mut v_i_5732_: *mut leanh::LeanObject,
    mut v_k_5733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5734_: u8 = 0;
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5734_ = lean_nat_dec_lt(v_k_5733_, v_hi_5729_);
                if v___x_5734_ == 0 {
                    leanh::lean_dec(v_k_5733_);
                    v___x_5735_ = lean_array_fswap(v_as_5731_, v_i_5732_, v_hi_5729_);
                    v___x_5736_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5736_, 0, v_i_5732_);
                    leanh::lean_ctor_set(v___x_5736_, 1, v___x_5735_);
                    return v___x_5736_;
                } else {
                    v___x_5737_ = lean_array_fget_borrowed(v_as_5731_, v_k_5733_);
                    v_fst_5738_ = leanh::lean_ctor_get(v___x_5737_, 0);
                    v_fst_5739_ = leanh::lean_ctor_get(v_pivot_5730_, 0);
                    v_fst_5740_ = leanh::lean_ctor_get(v_fst_5738_, 0);
                    v_fst_5741_ = leanh::lean_ctor_get(v_fst_5739_, 0);
                    v___x_5742_ = lean_nat_dec_lt(v_fst_5740_, v_fst_5741_);
                    if v___x_5742_ == 0 {
                        v___x_5743_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5744_ = lean_nat_add(v_k_5733_, v___x_5743_);
                        leanh::lean_dec(v_k_5733_);
                        v_k_5733_ = v___x_5744_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5746_ = lean_array_fswap(v_as_5731_, v_i_5732_, v_k_5733_);
                        v___x_5747_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5748_ = lean_nat_add(v_i_5732_, v___x_5747_);
                        leanh::lean_dec(v_i_5732_);
                        v___x_5749_ = lean_nat_add(v_k_5733_, v___x_5747_);
                        leanh::lean_dec(v_k_5733_);
                        v_as_5731_ = v___x_5746_;
                        v_i_5732_ = v___x_5748_;
                        v_k_5733_ = v___x_5749_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(
    mut v_hi_5751_: *mut leanh::LeanObject,
    mut v_pivot_5752_: *mut leanh::LeanObject,
    mut v_as_5753_: *mut leanh::LeanObject,
    mut v_i_5754_: *mut leanh::LeanObject,
    mut v_k_5755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_5751_, v_pivot_5752_, v_as_5753_, v_i_5754_, v_k_5755_);
    leanh::lean_dec_ref(v_pivot_5752_);
    leanh::lean_dec(v_hi_5751_);
    return v_res_5756_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(
    mut v_x_5757_: *mut leanh::LeanObject,
    mut v_x_5758_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: u8 = 0;
    v_fst_5759_ = leanh::lean_ctor_get(v_x_5757_, 0);
    v_fst_5760_ = leanh::lean_ctor_get(v_x_5758_, 0);
    v_fst_5761_ = leanh::lean_ctor_get(v_fst_5759_, 0);
    v_fst_5762_ = leanh::lean_ctor_get(v_fst_5760_, 0);
    v___x_5763_ = lean_nat_dec_lt(v_fst_5761_, v_fst_5762_);
    return v___x_5763_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(
    mut v_x_5764_: *mut leanh::LeanObject,
    mut v_x_5765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5766_: u8 = 0;
    let mut v_r_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5766_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_5764_, v_x_5765_);
    leanh::lean_dec_ref(v_x_5765_);
    leanh::lean_dec_ref(v_x_5764_);
    v_r_5767_ = leanh::lean_box((v_res_5766_) as usize);
    return v_r_5767_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(
    mut v_n_5768_: *mut leanh::LeanObject,
    mut v_as_5769_: *mut leanh::LeanObject,
    mut v_lo_5770_: *mut leanh::LeanObject,
    mut v_hi_5771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: u8 = 0;
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: u8 = 0;
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: u8 = 0;
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: u8 = 0;
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: u8 = 0;
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5783_ = lean_nat_dec_lt(v_lo_5770_, v_hi_5771_);
                if v___x_5783_ == 0 {
                    leanh::lean_dec(v_lo_5770_);
                    return v_as_5769_;
                } else {
                    v___x_5784_ = lean_nat_add(v_lo_5770_, v_hi_5771_);
                    v___x_5785_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_5786_ = lean_nat_shiftr(v___x_5784_, v___x_5785_);
                    leanh::lean_dec(v___x_5784_);
                    v___x_5799_ = lean_array_fget_borrowed(v_as_5769_, v_mid_5786_);
                    v___x_5800_ = lean_array_fget_borrowed(v_as_5769_, v_lo_5770_);
                    v___x_5801_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_5799_, v___x_5800_);
                    if v___x_5801_ == 0 {
                        v___y_5794_ = v_as_5769_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5802_ = lean_array_fswap(v_as_5769_, v_lo_5770_, v_mid_5786_);
                        v___y_5794_ = v___x_5802_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_5774_ = lean_array_fget(v___y_5773_, v_hi_5771_);
                leanh::lean_inc_n(v_lo_5770_, 2);
                v___x_5775_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_5771_, v_pivot_5774_, v___y_5773_, v_lo_5770_, v_lo_5770_);
                leanh::lean_dec(v_pivot_5774_);
                v_fst_5776_ = leanh::lean_ctor_get(v___x_5775_, 0);
                leanh::lean_inc(v_fst_5776_);
                v_snd_5777_ = leanh::lean_ctor_get(v___x_5775_, 1);
                leanh::lean_inc(v_snd_5777_);
                leanh::lean_dec_ref(v___x_5775_);
                v___x_5778_ = lean_nat_dec_le(v_hi_5771_, v_fst_5776_);
                if v___x_5778_ == 0 {
                    v___x_5779_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_5768_, v_snd_5777_, v_lo_5770_, v_fst_5776_);
                    v___x_5780_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5781_ = lean_nat_add(v_fst_5776_, v___x_5780_);
                    leanh::lean_dec(v_fst_5776_);
                    v_as_5769_ = v___x_5779_;
                    v_lo_5770_ = v___x_5781_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_5776_);
                    leanh::lean_dec(v_lo_5770_);
                    return v_snd_5777_;
                }
            }
            2 => {
                v___x_5789_ = lean_array_fget_borrowed(v___y_5788_, v_mid_5786_);
                v___x_5790_ = lean_array_fget_borrowed(v___y_5788_, v_hi_5771_);
                v___x_5791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_5789_, v___x_5790_);
                if v___x_5791_ == 0 {
                    leanh::lean_dec(v_mid_5786_);
                    v___y_5773_ = v___y_5788_;
                    state = 1;
                    continue;
                } else {
                    v___x_5792_ = lean_array_fswap(v___y_5788_, v_mid_5786_, v_hi_5771_);
                    leanh::lean_dec(v_mid_5786_);
                    v___y_5773_ = v___x_5792_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5795_ = lean_array_fget_borrowed(v___y_5794_, v_hi_5771_);
                v___x_5796_ = lean_array_fget_borrowed(v___y_5794_, v_lo_5770_);
                v___x_5797_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_5795_, v___x_5796_);
                if v___x_5797_ == 0 {
                    v___y_5788_ = v___y_5794_;
                    state = 2;
                    continue;
                } else {
                    v___x_5798_ = lean_array_fswap(v___y_5794_, v_lo_5770_, v_hi_5771_);
                    v___y_5788_ = v___x_5798_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(
    mut v_n_5803_: *mut leanh::LeanObject,
    mut v_as_5804_: *mut leanh::LeanObject,
    mut v_lo_5805_: *mut leanh::LeanObject,
    mut v_hi_5806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5807_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_5803_, v_as_5804_, v_lo_5805_, v_hi_5806_);
    leanh::lean_dec(v_hi_5806_);
    leanh::lean_dec(v_n_5803_);
    return v_res_5807_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5808_ = leanh::lean_box(0);
    v___x_5809_ = leanh::lean_unsigned_to_nat(16);
    v___x_5810_ = lean_mk_array(v___x_5809_, v___x_5808_);
    return v___x_5810_;
}
pub unsafe fn _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5811_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0),
        core::ptr::addr_of_mut!(l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once),
        _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0,
    );
    v___x_5812_ = leanh::lean_unsigned_to_nat(0);
    v_pos2traces_5813_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_pos2traces_5813_, 0, v___x_5812_);
    leanh::lean_ctor_set(v_pos2traces_5813_, 1, v___x_5811_);
    return v_pos2traces_5813_;
}
pub unsafe fn l_Lean_addTraceAsMessages___at___00main_spec__10(
    mut v___y_5814_: *mut leanh::LeanObject,
    mut v___y_5815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v___x_5830_: u8 = 0;
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos2traces_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5838_: usize = 0;
    let mut v___x_5839_: usize = 0;
    let mut v___x_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5847_: u8 = 0;
    let mut v_unused_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: u8 = 0;
    let mut v___y_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: u8 = 0;
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: u8 = 0;
    let mut v_size_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: u8 = 0;
    let mut v___x_5873_: u8 = 0;
    let mut v___x_5874_: usize = 0;
    let mut v___x_5875_: usize = 0;
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: usize = 0;
    let mut v___x_5878_: usize = 0;
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5887_: u8 = 0;
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5820_ = leanh::lean_ctor_get(v___y_5814_, 2);
                v___x_5821_ = l_Lean_trace_profiler_output;
                v___x_5822_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_5820_, v___x_5821_);
                if leanh::lean_obj_tag(v___x_5822_) == 0 {
                    v___x_5823_ = l_Lean_trace_profiler_serve;
                    v___x_5824_ =
                        l_Lean_Option_get___at___00main_spec__8(v_options_5820_, v___x_5823_);
                    if v___x_5824_ == 0 {
                        v___x_5825_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_5815_);
                        v_a_5826_ = leanh::lean_ctor_get(v___x_5825_, 0);
                        v_isSharedCheck_5892_ =
                            (!leanh::lean_is_exclusive(v___x_5825_)) as u8;
                        if v_isSharedCheck_5892_ == 0 {
                            v___x_5828_ = v___x_5825_;
                            v_isShared_5829_ = v_isSharedCheck_5892_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5826_);
                            leanh::lean_dec(v___x_5825_);
                            v___x_5828_ = leanh::lean_box(0);
                            v_isShared_5829_ = v_isSharedCheck_5892_;
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_5822_, 1);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5818_ = leanh::lean_box(0);
                v___x_5819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5819_, 0, v___x_5818_);
                return v___x_5819_;
            }
            2 => {
                v___x_5830_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_5826_);
                if v___x_5830_ == 0 {
                    leanh::lean_del_object(v___x_5828_);
                    v___x_5831_ = leanh::lean_unsigned_to_nat(0);
                    v_pos2traces_5832_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once
                        ),
                        _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1,
                    );
                    v___x_5833_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_5830_, v_a_5826_, v_pos2traces_5832_, v___y_5814_, v___y_5815_);
                    leanh::lean_dec(v_a_5826_);
                    if leanh::lean_obj_tag(v___x_5833_) == 0 {
                        v_a_5834_ = leanh::lean_ctor_get(v___x_5833_, 0);
                        leanh::lean_inc(v_a_5834_);
                        leanh::lean_dec_ref_known(v___x_5833_, 1);
                        v_size_5868_ = leanh::lean_ctor_get(v_a_5834_, 0);
                        leanh::lean_inc(v_size_5868_);
                        v_buckets_5869_ = leanh::lean_ctor_get(v_a_5834_, 1);
                        leanh::lean_inc_ref(v_buckets_5869_);
                        leanh::lean_dec(v_a_5834_);
                        v___x_5870_ = lean_mk_empty_array_with_capacity(v_size_5868_);
                        leanh::lean_dec(v_size_5868_);
                        v___x_5871_ = lean_array_get_size(v_buckets_5869_);
                        v___x_5872_ = lean_nat_dec_lt(v___x_5831_, v___x_5871_);
                        if v___x_5872_ == 0 {
                            leanh::lean_dec_ref(v_buckets_5869_);
                            v___y_5862_ = v___x_5870_;
                            state = 8;
                            continue;
                        } else {
                            v___x_5873_ = lean_nat_dec_le(v___x_5871_, v___x_5871_);
                            if v___x_5873_ == 0 {
                                if v___x_5872_ == 0 {
                                    leanh::lean_dec_ref(v_buckets_5869_);
                                    v___y_5862_ = v___x_5870_;
                                    state = 8;
                                    continue;
                                } else {
                                    v___x_5874_ = 0usize;
                                    v___x_5875_ = lean_usize_of_nat(v___x_5871_);
                                    v___x_5876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_5869_, v___x_5874_, v___x_5875_, v___x_5870_);
                                    leanh::lean_dec_ref(v_buckets_5869_);
                                    v___y_5862_ = v___x_5876_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v___x_5877_ = 0usize;
                                v___x_5878_ = lean_usize_of_nat(v___x_5871_);
                                v___x_5879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_5869_, v___x_5877_, v___x_5878_, v___x_5870_);
                                leanh::lean_dec_ref(v_buckets_5869_);
                                v___y_5862_ = v___x_5879_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v_a_5880_ = leanh::lean_ctor_get(v___x_5833_, 0);
                        v_isSharedCheck_5887_ =
                            (!leanh::lean_is_exclusive(v___x_5833_)) as u8;
                        if v_isSharedCheck_5887_ == 0 {
                            v___x_5882_ = v___x_5833_;
                            v_isShared_5883_ = v_isSharedCheck_5887_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5880_);
                            leanh::lean_dec(v___x_5833_);
                            v___x_5882_ = leanh::lean_box(0);
                            v_isShared_5883_ = v_isSharedCheck_5887_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5826_);
                    v___x_5888_ = leanh::lean_box(0);
                    if v_isShared_5829_ == 0 {
                        leanh::lean_ctor_set(v___x_5828_, 0, v___x_5888_);
                        v___x_5890_ = v___x_5828_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5891_, 0, v___x_5888_);
                        v___x_5890_ = v_reuseFailAlloc_5891_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5837_ = leanh::lean_box(0);
                v_sz_5838_ = lean_array_size(v___y_5836_);
                v___x_5839_ = 0usize;
                v___x_5840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_5824_, v___y_5836_, v_sz_5838_, v___x_5839_, v___x_5837_, v___y_5814_, v___y_5815_);
                leanh::lean_dec_ref(v___y_5836_);
                if leanh::lean_obj_tag(v___x_5840_) == 0 {
                    v_isSharedCheck_5847_ = (!leanh::lean_is_exclusive(v___x_5840_)) as u8;
                    if v_isSharedCheck_5847_ == 0 {
                        v_unused_5848_ = leanh::lean_ctor_get(v___x_5840_, 0);
                        leanh::lean_dec(v_unused_5848_);
                        v___x_5842_ = v___x_5840_;
                        v_isShared_5843_ = v_isSharedCheck_5847_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5840_);
                        v___x_5842_ = leanh::lean_box(0);
                        v_isShared_5843_ = v_isSharedCheck_5847_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___x_5840_;
                }
            }
            4 => {
                if v_isShared_5843_ == 0 {
                    leanh::lean_ctor_set(v___x_5842_, 0, v___x_5837_);
                    v___x_5845_ = v___x_5842_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5846_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5837_);
                    v___x_5845_ = v_reuseFailAlloc_5846_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5845_;
            }
            6 => {
                v___x_5854_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
                leanh::lean_dec(v___y_5853_);
                leanh::lean_dec(v___y_5850_);
                v___y_5836_ = v___x_5854_;
                state = 3;
                continue;
            }
            7 => {
                v___x_5860_ = lean_nat_dec_le(v___y_5859_, v___y_5857_);
                if v___x_5860_ == 0 {
                    leanh::lean_dec(v___y_5857_);
                    leanh::lean_inc(v___y_5859_);
                    v___y_5850_ = v___y_5856_;
                    v___y_5851_ = v___y_5858_;
                    v___y_5852_ = v___y_5859_;
                    v___y_5853_ = v___y_5859_;
                    state = 6;
                    continue;
                } else {
                    v___y_5850_ = v___y_5856_;
                    v___y_5851_ = v___y_5858_;
                    v___y_5852_ = v___y_5859_;
                    v___y_5853_ = v___y_5857_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_5863_ = lean_array_get_size(v___y_5862_);
                v___x_5864_ = lean_nat_dec_eq(v___x_5863_, v___x_5831_);
                if v___x_5864_ == 0 {
                    v___x_5865_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5866_ = lean_nat_sub(v___x_5863_, v___x_5865_);
                    v___x_5867_ = lean_nat_dec_le(v___x_5831_, v___x_5866_);
                    if v___x_5867_ == 0 {
                        leanh::lean_inc(v___x_5866_);
                        v___y_5856_ = v___x_5863_;
                        v___y_5857_ = v___x_5866_;
                        v___y_5858_ = v___y_5862_;
                        v___y_5859_ = v___x_5866_;
                        state = 7;
                        continue;
                    } else {
                        v___y_5856_ = v___x_5863_;
                        v___y_5857_ = v___x_5866_;
                        v___y_5858_ = v___y_5862_;
                        v___y_5859_ = v___x_5831_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_5836_ = v___y_5862_;
                    state = 3;
                    continue;
                }
            }
            9 => {
                if v_isShared_5883_ == 0 {
                    v___x_5885_ = v___x_5882_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5886_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_a_5880_);
                    v___x_5885_ = v_reuseFailAlloc_5886_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5885_;
            }
            11 => {
                return v___x_5890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(
    mut v___y_5893_: *mut leanh::LeanObject,
    mut v___y_5894_: *mut leanh::LeanObject,
    mut v___y_5895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5896_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_5893_, v___y_5894_);
    leanh::lean_dec(v___y_5894_);
    leanh::lean_dec_ref(v___y_5893_);
    return v_res_5896_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(
    mut v_as_5897_: *mut leanh::LeanObject,
    mut v_sz_5898_: usize,
    mut v_i_5899_: usize,
    mut v_b_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
    mut v___y_5902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5904_: u8 = 0;
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: usize = 0;
    let mut v___x_5912_: usize = 0;
    let mut v_a_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5918_: u8 = 0;
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5922_: u8 = 0;
    let mut v_unused_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5904_ = lean_usize_dec_lt(v_i_5899_, v_sz_5898_);
                if v___x_5904_ == 0 {
                    v___x_5905_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5905_, 0, v_b_5900_);
                    return v___x_5905_;
                } else {
                    v_options_5906_ = leanh::lean_ctor_get(v___y_5901_, 2);
                    v_a_5907_ = lean_array_uget_borrowed(v_as_5897_, v_i_5899_);
                    leanh::lean_inc_ref(v_options_5906_);
                    leanh::lean_inc(v_a_5907_);
                    v___x_5908_ = l_Lean_Compiler_LCNF_resumeCompilation(
                        v_a_5907_,
                        v_options_5906_,
                        v___y_5901_,
                        v___y_5902_,
                    );
                    if leanh::lean_obj_tag(v___x_5908_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5908_, 1);
                        v___x_5909_ = l_Lean_addTraceAsMessages___at___00main_spec__10(
                            v___y_5901_,
                            v___y_5902_,
                        );
                        if leanh::lean_obj_tag(v___x_5909_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5909_, 1);
                            v___x_5910_ = leanh::lean_box(0);
                            v___x_5911_ = 1usize;
                            v___x_5912_ = lean_usize_add(v_i_5899_, v___x_5911_);
                            v_i_5899_ = v___x_5912_;
                            v_b_5900_ = v___x_5910_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_5909_;
                        }
                    } else {
                        v_a_5914_ = leanh::lean_ctor_get(v___x_5908_, 0);
                        leanh::lean_inc(v_a_5914_);
                        leanh::lean_dec_ref_known(v___x_5908_, 1);
                        v___x_5915_ = l_Lean_addTraceAsMessages___at___00main_spec__10(
                            v___y_5901_,
                            v___y_5902_,
                        );
                        if leanh::lean_obj_tag(v___x_5915_) == 0 {
                            v_isSharedCheck_5922_ =
                                (!leanh::lean_is_exclusive(v___x_5915_)) as u8;
                            if v_isSharedCheck_5922_ == 0 {
                                v_unused_5923_ = leanh::lean_ctor_get(v___x_5915_, 0);
                                leanh::lean_dec(v_unused_5923_);
                                v___x_5917_ = v___x_5915_;
                                v_isShared_5918_ = v_isSharedCheck_5922_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5915_);
                                v___x_5917_ = leanh::lean_box(0);
                                v_isShared_5918_ = v_isSharedCheck_5922_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5914_);
                            return v___x_5915_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5918_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5917_, 1);
                    leanh::lean_ctor_set(v___x_5917_, 0, v_a_5914_);
                    v___x_5920_ = v___x_5917_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5921_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5921_, 0, v_a_5914_);
                    v___x_5920_ = v_reuseFailAlloc_5921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(
    mut v_as_5924_: *mut leanh::LeanObject,
    mut v_sz_5925_: *mut leanh::LeanObject,
    mut v_i_5926_: *mut leanh::LeanObject,
    mut v_b_5927_: *mut leanh::LeanObject,
    mut v___y_5928_: *mut leanh::LeanObject,
    mut v___y_5929_: *mut leanh::LeanObject,
    mut v___y_5930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5931_: usize = 0;
    let mut v_i_boxed_5932_: usize = 0;
    let mut v_res_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5931_ = leanh::lean_unbox_usize(v_sz_5925_);
    leanh::lean_dec(v_sz_5925_);
    v_i_boxed_5932_ = leanh::lean_unbox_usize(v_i_5926_);
    leanh::lean_dec(v_i_5926_);
    v_res_5933_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(
            v_as_5924_,
            v_sz_boxed_5931_,
            v_i_boxed_5932_,
            v_b_5927_,
            v___y_5928_,
            v___y_5929_,
        );
    leanh::lean_dec(v___y_5929_);
    leanh::lean_dec_ref(v___y_5928_);
    leanh::lean_dec_ref(v_as_5924_);
    return v_res_5933_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(
    mut v_as_5934_: *mut leanh::LeanObject,
    mut v_sz_5935_: usize,
    mut v_i_5936_: usize,
    mut v_b_5937_: *mut leanh::LeanObject,
    mut v___y_5938_: *mut leanh::LeanObject,
    mut v___y_5939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5941_: u8 = 0;
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declNames_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5946_: usize = 0;
    let mut v___x_5947_: usize = 0;
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unreported_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: usize = 0;
    let mut v___x_5954_: usize = 0;
    let mut v_a_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5959_: u8 = 0;
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5941_ = lean_usize_dec_lt(v_i_5936_, v_sz_5935_);
                if v___x_5941_ == 0 {
                    v___x_5942_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5942_, 0, v_b_5937_);
                    return v___x_5942_;
                } else {
                    v_a_5943_ = lean_array_uget_borrowed(v_as_5934_, v_i_5936_);
                    v_declNames_5944_ = leanh::lean_ctor_get(v_a_5943_, 0);
                    v___x_5945_ = leanh::lean_box(0);
                    v_sz_5946_ = lean_array_size(v_declNames_5944_);
                    v___x_5947_ = 0usize;
                    v___x_5948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_5944_, v_sz_5946_, v___x_5947_, v___x_5945_, v___y_5938_, v___y_5939_);
                    if leanh::lean_obj_tag(v___x_5948_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5948_, 1);
                        v___x_5949_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_5939_);
                        if leanh::lean_obj_tag(v___x_5949_) == 0 {
                            v_a_5950_ = leanh::lean_ctor_get(v___x_5949_, 0);
                            leanh::lean_inc(v_a_5950_);
                            leanh::lean_dec_ref_known(v___x_5949_, 1);
                            v_unreported_5951_ = leanh::lean_ctor_get(v_a_5950_, 1);
                            leanh::lean_inc_ref(v_unreported_5951_);
                            leanh::lean_dec(v_a_5950_);
                            v___x_5952_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(
                                v_unreported_5951_,
                                v___x_5945_,
                                v___y_5938_,
                                v___y_5939_,
                            );
                            leanh::lean_dec_ref(v_unreported_5951_);
                            if leanh::lean_obj_tag(v___x_5952_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5952_, 1);
                                v___x_5953_ = 1usize;
                                v___x_5954_ = lean_usize_add(v_i_5936_, v___x_5953_);
                                v_i_5936_ = v___x_5954_;
                                v_b_5937_ = v___x_5945_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_5952_;
                            }
                        } else {
                            v_a_5956_ = leanh::lean_ctor_get(v___x_5949_, 0);
                            v_isSharedCheck_5963_ =
                                (!leanh::lean_is_exclusive(v___x_5949_)) as u8;
                            if v_isSharedCheck_5963_ == 0 {
                                v___x_5958_ = v___x_5949_;
                                v_isShared_5959_ = v_isSharedCheck_5963_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5956_);
                                leanh::lean_dec(v___x_5949_);
                                v___x_5958_ = leanh::lean_box(0);
                                v_isShared_5959_ = v_isSharedCheck_5963_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        return v___x_5948_;
                    }
                }
            }
            1 => {
                if v_isShared_5959_ == 0 {
                    v___x_5961_ = v___x_5958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
                    v___x_5961_ = v_reuseFailAlloc_5962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(
    mut v_as_5964_: *mut leanh::LeanObject,
    mut v_sz_5965_: *mut leanh::LeanObject,
    mut v_i_5966_: *mut leanh::LeanObject,
    mut v_b_5967_: *mut leanh::LeanObject,
    mut v___y_5968_: *mut leanh::LeanObject,
    mut v___y_5969_: *mut leanh::LeanObject,
    mut v___y_5970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5971_: usize = 0;
    let mut v_i_boxed_5972_: usize = 0;
    let mut v_res_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5971_ = leanh::lean_unbox_usize(v_sz_5965_);
    leanh::lean_dec(v_sz_5965_);
    v_i_boxed_5972_ = leanh::lean_unbox_usize(v_i_5966_);
    leanh::lean_dec(v_i_5966_);
    v_res_5973_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(
            v_as_5964_,
            v_sz_boxed_5971_,
            v_i_boxed_5972_,
            v_b_5967_,
            v___y_5968_,
            v___y_5969_,
        );
    leanh::lean_dec(v___y_5969_);
    leanh::lean_dec_ref(v___y_5968_);
    leanh::lean_dec_ref(v_as_5964_);
    return v_res_5973_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(
    mut v_as_5974_: *mut leanh::LeanObject,
    mut v_i_5975_: usize,
    mut v_stop_5976_: usize,
    mut v_b_5977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5978_: u8 = 0;
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: usize = 0;
    let mut v___x_5983_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5978_ = lean_usize_dec_eq(v_i_5975_, v_stop_5976_);
                if v___x_5978_ == 0 {
                    v___x_5979_ = lean_array_uget_borrowed(v_as_5974_, v_i_5975_);
                    v_name_5980_ = leanh::lean_ctor_get(v___x_5979_, 0);
                    leanh::lean_inc(v_name_5980_);
                    v___x_5981_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_5977_, v_name_5980_);
                    v___x_5982_ = 1usize;
                    v___x_5983_ = lean_usize_add(v_i_5975_, v___x_5982_);
                    v_i_5975_ = v___x_5983_;
                    v_b_5977_ = v___x_5981_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5977_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(
    mut v_as_5985_: *mut leanh::LeanObject,
    mut v_i_5986_: *mut leanh::LeanObject,
    mut v_stop_5987_: *mut leanh::LeanObject,
    mut v_b_5988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5989_: usize = 0;
    let mut v_stop_boxed_5990_: usize = 0;
    let mut v_res_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5989_ = leanh::lean_unbox_usize(v_i_5986_);
    leanh::lean_dec(v_i_5986_);
    v_stop_boxed_5990_ = leanh::lean_unbox_usize(v_stop_5987_);
    leanh::lean_dec(v_stop_5987_);
    v_res_5991_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(
            v_as_5985_,
            v_i_boxed_5989_,
            v_stop_boxed_5990_,
            v_b_5988_,
        );
    leanh::lean_dec_ref(v_as_5985_);
    return v_res_5991_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(
    mut v___y_5992_: u8,
    mut v_suppressElabErrors_5993_: u8,
    mut v_x_5994_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_5994_) == 1 {
        let mut v_pre_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_5995_ = leanh::lean_ctor_get(v_x_5994_, 0);
        match leanh::lean_obj_tag(v_pre_5995_) {
            1 => {
                let mut v_pre_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_5996_ = leanh::lean_ctor_get(v_pre_5995_, 0);
                match leanh::lean_obj_tag(v_pre_5996_) {
                    0 => {
                        let mut v_str_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6000_: u8 = 0;
                        v_str_5997_ = leanh::lean_ctor_get(v_x_5994_, 1);
                        v_str_5998_ = leanh::lean_ctor_get(v_pre_5995_, 1);
                        v___x_5999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0;
                        v___x_6000_ = lean_string_dec_eq(v_str_5998_, v___x_5999_);
                        if v___x_6000_ == 0 {
                            let mut v___x_6001_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6002_: u8 = 0;
                            v___x_6001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1;
                            v___x_6002_ = lean_string_dec_eq(v_str_5998_, v___x_6001_);
                            if v___x_6002_ == 0 {
                                return v___y_5992_;
                            } else {
                                let mut v___x_6003_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6004_: u8 = 0;
                                v___x_6003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2;
                                v___x_6004_ = lean_string_dec_eq(v_str_5997_, v___x_6003_);
                                if v___x_6004_ == 0 {
                                    return v___y_5992_;
                                } else {
                                    return v_suppressElabErrors_5993_;
                                }
                            }
                        } else {
                            let mut v___x_6005_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6006_: u8 = 0;
                            v___x_6005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3;
                            v___x_6006_ = lean_string_dec_eq(v_str_5997_, v___x_6005_);
                            if v___x_6006_ == 0 {
                                return v___y_5992_;
                            } else {
                                return v_suppressElabErrors_5993_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_6007_ = leanh::lean_ctor_get(v_pre_5996_, 0);
                        if leanh::lean_obj_tag(v_pre_6007_) == 0 {
                            let mut v_str_6008_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6009_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6010_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6011_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6012_: u8 = 0;
                            v_str_6008_ = leanh::lean_ctor_get(v_x_5994_, 1);
                            v_str_6009_ = leanh::lean_ctor_get(v_pre_5995_, 1);
                            v_str_6010_ = leanh::lean_ctor_get(v_pre_5996_, 1);
                            v___x_6011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4;
                            v___x_6012_ = lean_string_dec_eq(v_str_6010_, v___x_6011_);
                            if v___x_6012_ == 0 {
                                return v___y_5992_;
                            } else {
                                let mut v___x_6013_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6014_: u8 = 0;
                                v___x_6013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5;
                                v___x_6014_ = lean_string_dec_eq(v_str_6009_, v___x_6013_);
                                if v___x_6014_ == 0 {
                                    return v___y_5992_;
                                } else {
                                    let mut v___x_6015_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_6016_: u8 = 0;
                                    v___x_6015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6;
                                    v___x_6016_ = lean_string_dec_eq(v_str_6008_, v___x_6015_);
                                    if v___x_6016_ == 0 {
                                        return v___y_5992_;
                                    } else {
                                        return v_suppressElabErrors_5993_;
                                    }
                                }
                            }
                        } else {
                            return v___y_5992_;
                        }
                    }
                    _ => {
                        return v___y_5992_;
                    }
                }
            }
            0 => {
                let mut v_str_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6019_: u8 = 0;
                v_str_6017_ = leanh::lean_ctor_get(v_x_5994_, 1);
                v___x_6018_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0;
                v___x_6019_ = lean_string_dec_eq(v_str_6017_, v___x_6018_);
                if v___x_6019_ == 0 {
                    return v___y_5992_;
                } else {
                    return v_suppressElabErrors_5993_;
                }
            }
            _ => {
                return v___y_5992_;
            }
        }
    } else {
        return v___y_5992_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(
    mut v___y_6020_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_6021_: *mut leanh::LeanObject,
    mut v_x_6022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_38886__boxed_6023_: u8 = 0;
    let mut v_suppressElabErrors_boxed_6024_: u8 = 0;
    let mut v_res_6025_: u8 = 0;
    let mut v_r_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_38886__boxed_6023_ = (leanh::lean_unbox(v___y_6020_) as u8);
    v_suppressElabErrors_boxed_6024_ = (leanh::lean_unbox(v_suppressElabErrors_6021_) as u8);
    v_res_6025_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38886__boxed_6023_, v_suppressElabErrors_boxed_6024_, v_x_6022_);
    leanh::lean_dec(v_x_6022_);
    v_r_6026_ = leanh::lean_box((v_res_6025_) as usize);
    return v_r_6026_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(
    mut v_ref_6027_: *mut leanh::LeanObject,
    mut v_msgData_6028_: *mut leanh::LeanObject,
    mut v_severity_6029_: u8,
    mut v_isSilent_6030_: u8,
    mut v___y_6031_: *mut leanh::LeanObject,
    mut v___y_6032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6035_: u8 = 0;
    let mut v___y_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6041_: u8 = 0;
    let mut v___y_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6058_: u8 = 0;
    let mut v___x_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6069_: u8 = 0;
    let mut v___y_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6073_: u8 = 0;
    let mut v___y_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6076_: u8 = 0;
    let mut v___y_6077_: u8 = 0;
    let mut v___y_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6084_: u8 = 0;
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: u8 = 0;
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6094_: u8 = 0;
    let mut v___y_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6098_: u8 = 0;
    let mut v___y_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: u8 = 0;
    let mut v___y_6102_: u8 = 0;
    let mut v___y_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: u8 = 0;
    let mut v___y_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6111_: u8 = 0;
    let mut v___y_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6113_: u8 = 0;
    let mut v_ref_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: u8 = 0;
    let mut v___y_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6122_: u8 = 0;
    let mut v___y_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6125_: u8 = 0;
    let mut v___y_6126_: u8 = 0;
    let mut v___y_6128_: u8 = 0;
    let mut v_fileName_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6133_: u8 = 0;
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: u8 = 0;
    let mut v___x_6138_: u8 = 0;
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: u8 = 0;
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: u8 = 0;
    let mut v___x_6144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6118_ = 2;
                v___x_6143_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6029_, v___x_6118_);
                if v___x_6143_ == 0 {
                    v___y_6128_ = v___x_6143_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_6028_);
                    v___x_6144_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6028_);
                    v___y_6128_ = v___x_6144_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_6044_ = lean_st_ref_take(v___y_6043_);
                v_currNamespace_6045_ = leanh::lean_ctor_get(v___y_6042_, 6);
                v_openDecls_6046_ = leanh::lean_ctor_get(v___y_6042_, 7);
                v_env_6047_ = leanh::lean_ctor_get(v___x_6044_, 0);
                v_nextMacroScope_6048_ = leanh::lean_ctor_get(v___x_6044_, 1);
                v_ngen_6049_ = leanh::lean_ctor_get(v___x_6044_, 2);
                v_auxDeclNGen_6050_ = leanh::lean_ctor_get(v___x_6044_, 3);
                v_traceState_6051_ = leanh::lean_ctor_get(v___x_6044_, 4);
                v_cache_6052_ = leanh::lean_ctor_get(v___x_6044_, 5);
                v_messages_6053_ = leanh::lean_ctor_get(v___x_6044_, 6);
                v_infoState_6054_ = leanh::lean_ctor_get(v___x_6044_, 7);
                v_snapshotTasks_6055_ = leanh::lean_ctor_get(v___x_6044_, 8);
                v_isSharedCheck_6069_ = (!leanh::lean_is_exclusive(v___x_6044_)) as u8;
                if v_isSharedCheck_6069_ == 0 {
                    v___x_6057_ = v___x_6044_;
                    v_isShared_6058_ = v_isSharedCheck_6069_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6055_);
                    leanh::lean_inc(v_infoState_6054_);
                    leanh::lean_inc(v_messages_6053_);
                    leanh::lean_inc(v_cache_6052_);
                    leanh::lean_inc(v_traceState_6051_);
                    leanh::lean_inc(v_auxDeclNGen_6050_);
                    leanh::lean_inc(v_ngen_6049_);
                    leanh::lean_inc(v_nextMacroScope_6048_);
                    leanh::lean_inc(v_env_6047_);
                    leanh::lean_dec(v___x_6044_);
                    v___x_6057_ = leanh::lean_box(0);
                    v_isShared_6058_ = v_isSharedCheck_6069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_6046_);
                leanh::lean_inc(v_currNamespace_6045_);
                v___x_6059_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6059_, 0, v_currNamespace_6045_);
                leanh::lean_ctor_set(v___x_6059_, 1, v_openDecls_6046_);
                v___x_6060_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6060_, 0, v___x_6059_);
                leanh::lean_ctor_set(v___x_6060_, 1, v___y_6040_);
                leanh::lean_inc_ref(v___y_6039_);
                leanh::lean_inc_ref(v___y_6037_);
                v___x_6061_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_6061_, 0, v___y_6037_);
                leanh::lean_ctor_set(v___x_6061_, 1, v___y_6038_);
                leanh::lean_ctor_set(v___x_6061_, 2, v___y_6036_);
                leanh::lean_ctor_set(v___x_6061_, 3, v___y_6039_);
                leanh::lean_ctor_set(v___x_6061_, 4, v___x_6060_);
                leanh::lean_ctor_set_uint8(
                    v___x_6061_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_6035_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6061_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_6041_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6061_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_6030_,
                );
                v___x_6062_ = l_Lean_MessageLog_add(v___x_6061_, v_messages_6053_);
                if v_isShared_6058_ == 0 {
                    leanh::lean_ctor_set(v___x_6057_, 6, v___x_6062_);
                    v___x_6064_ = v___x_6057_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6068_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 0, v_env_6047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 1, v_nextMacroScope_6048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 2, v_ngen_6049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 3, v_auxDeclNGen_6050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 4, v_traceState_6051_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 5, v_cache_6052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 6, v___x_6062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 7, v_infoState_6054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 8, v_snapshotTasks_6055_);
                    v___x_6064_ = v_reuseFailAlloc_6068_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6065_ = lean_st_ref_set(v___y_6043_, v___x_6064_);
                v___x_6066_ = leanh::lean_box(0);
                v___x_6067_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6067_, 0, v___x_6066_);
                return v___x_6067_;
            }
            4 => {
                v___x_6079_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_6028_,
                    );
                v___x_6080_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_6079_, v___y_6031_, v___y_6032_);
                v_a_6081_ = leanh::lean_ctor_get(v___x_6080_, 0);
                v_isSharedCheck_6094_ = (!leanh::lean_is_exclusive(v___x_6080_)) as u8;
                if v_isSharedCheck_6094_ == 0 {
                    v___x_6083_ = v___x_6080_;
                    v_isShared_6084_ = v_isSharedCheck_6094_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6081_);
                    leanh::lean_dec(v___x_6080_);
                    v___x_6083_ = leanh::lean_box(0);
                    v_isShared_6084_ = v_isSharedCheck_6094_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_6072_, 2);
                v___x_6085_ = l_Lean_FileMap_toPosition(v___y_6072_, v___y_6075_);
                leanh::lean_dec(v___y_6075_);
                v___x_6086_ = l_Lean_FileMap_toPosition(v___y_6072_, v___y_6078_);
                leanh::lean_dec(v___y_6078_);
                v___x_6087_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6087_, 0, v___x_6086_);
                v___x_6088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1;
                if v___y_6076_ == 0 {
                    leanh::lean_del_object(v___x_6083_);
                    leanh::lean_dec_ref(v___y_6071_);
                    v___y_6035_ = v___y_6073_;
                    v___y_6036_ = v___x_6087_;
                    v___y_6037_ = v___y_6074_;
                    v___y_6038_ = v___x_6085_;
                    v___y_6039_ = v___x_6088_;
                    v___y_6040_ = v_a_6081_;
                    v___y_6041_ = v___y_6077_;
                    v___y_6042_ = v___y_6031_;
                    v___y_6043_ = v___y_6032_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6081_);
                    v___x_6089_ = l_Lean_MessageData_hasTag(v___y_6071_, v_a_6081_);
                    if v___x_6089_ == 0 {
                        leanh::lean_dec_ref_known(v___x_6087_, 1);
                        leanh::lean_dec_ref(v___x_6085_);
                        leanh::lean_dec(v_a_6081_);
                        v___x_6090_ = leanh::lean_box(0);
                        if v_isShared_6084_ == 0 {
                            leanh::lean_ctor_set(v___x_6083_, 0, v___x_6090_);
                            v___x_6092_ = v___x_6083_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6093_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 0, v___x_6090_);
                            v___x_6092_ = v_reuseFailAlloc_6093_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6083_);
                        v___y_6035_ = v___y_6073_;
                        v___y_6036_ = v___x_6087_;
                        v___y_6037_ = v___y_6074_;
                        v___y_6038_ = v___x_6085_;
                        v___y_6039_ = v___x_6088_;
                        v___y_6040_ = v_a_6081_;
                        v___y_6041_ = v___y_6077_;
                        v___y_6042_ = v___y_6031_;
                        v___y_6043_ = v___y_6032_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_6092_;
            }
            7 => {
                v___x_6104_ = l_Lean_Syntax_getTailPos_x3f(v___y_6100_, v___y_6098_);
                leanh::lean_dec(v___y_6100_);
                if leanh::lean_obj_tag(v___x_6104_) == 0 {
                    leanh::lean_inc(v___y_6103_);
                    v___y_6071_ = v___y_6096_;
                    v___y_6072_ = v___y_6097_;
                    v___y_6073_ = v___y_6098_;
                    v___y_6074_ = v___y_6099_;
                    v___y_6075_ = v___y_6103_;
                    v___y_6076_ = v___y_6101_;
                    v___y_6077_ = v___y_6102_;
                    v___y_6078_ = v___y_6103_;
                    state = 4;
                    continue;
                } else {
                    v_val_6105_ = leanh::lean_ctor_get(v___x_6104_, 0);
                    leanh::lean_inc(v_val_6105_);
                    leanh::lean_dec_ref_known(v___x_6104_, 1);
                    v___y_6071_ = v___y_6096_;
                    v___y_6072_ = v___y_6097_;
                    v___y_6073_ = v___y_6098_;
                    v___y_6074_ = v___y_6099_;
                    v___y_6075_ = v___y_6103_;
                    v___y_6076_ = v___y_6101_;
                    v___y_6077_ = v___y_6102_;
                    v___y_6078_ = v_val_6105_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_6114_ = l_Lean_replaceRef(v_ref_6027_, v___y_6112_);
                v___x_6115_ = l_Lean_Syntax_getPos_x3f(v_ref_6114_, v___y_6109_);
                if leanh::lean_obj_tag(v___x_6115_) == 0 {
                    v___x_6116_ = leanh::lean_unsigned_to_nat(0);
                    v___y_6096_ = v___y_6107_;
                    v___y_6097_ = v___y_6108_;
                    v___y_6098_ = v___y_6109_;
                    v___y_6099_ = v___y_6110_;
                    v___y_6100_ = v_ref_6114_;
                    v___y_6101_ = v___y_6111_;
                    v___y_6102_ = v___y_6113_;
                    v___y_6103_ = v___x_6116_;
                    state = 7;
                    continue;
                } else {
                    v_val_6117_ = leanh::lean_ctor_get(v___x_6115_, 0);
                    leanh::lean_inc(v_val_6117_);
                    leanh::lean_dec_ref_known(v___x_6115_, 1);
                    v___y_6096_ = v___y_6107_;
                    v___y_6097_ = v___y_6108_;
                    v___y_6098_ = v___y_6109_;
                    v___y_6099_ = v___y_6110_;
                    v___y_6100_ = v_ref_6114_;
                    v___y_6101_ = v___y_6111_;
                    v___y_6102_ = v___y_6113_;
                    v___y_6103_ = v_val_6117_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_6126_ == 0 {
                    v___y_6107_ = v___y_6123_;
                    v___y_6108_ = v___y_6120_;
                    v___y_6109_ = v___y_6125_;
                    v___y_6110_ = v___y_6121_;
                    v___y_6111_ = v___y_6122_;
                    v___y_6112_ = v___y_6124_;
                    v___y_6113_ = v_severity_6029_;
                    state = 8;
                    continue;
                } else {
                    v___y_6107_ = v___y_6123_;
                    v___y_6108_ = v___y_6120_;
                    v___y_6109_ = v___y_6125_;
                    v___y_6110_ = v___y_6121_;
                    v___y_6111_ = v___y_6122_;
                    v___y_6112_ = v___y_6124_;
                    v___y_6113_ = v___x_6118_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_6128_ == 0 {
                    v_fileName_6129_ = leanh::lean_ctor_get(v___y_6031_, 0);
                    v_fileMap_6130_ = leanh::lean_ctor_get(v___y_6031_, 1);
                    v_options_6131_ = leanh::lean_ctor_get(v___y_6031_, 2);
                    v_ref_6132_ = leanh::lean_ctor_get(v___y_6031_, 5);
                    v_suppressElabErrors_6133_ = leanh::lean_ctor_get_uint8(
                        v___y_6031_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_6134_ = leanh::lean_box((v___y_6128_) as usize);
                    v___x_6135_ = leanh::lean_box((v_suppressElabErrors_6133_) as usize);
                    v___f_6136_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_6136_, 0, v___x_6134_);
                    leanh::lean_closure_set(v___f_6136_, 1, v___x_6135_);
                    v___x_6137_ = 1;
                    v___x_6138_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6029_, v___x_6137_);
                    if v___x_6138_ == 0 {
                        v___y_6120_ = v_fileMap_6130_;
                        v___y_6121_ = v_fileName_6129_;
                        v___y_6122_ = v_suppressElabErrors_6133_;
                        v___y_6123_ = v___f_6136_;
                        v___y_6124_ = v_ref_6132_;
                        v___y_6125_ = v___y_6128_;
                        v___y_6126_ = v___x_6138_;
                        state = 9;
                        continue;
                    } else {
                        v___x_6139_ = l_Lean_warningAsError;
                        v___x_6140_ =
                            l_Lean_Option_get___at___00main_spec__8(v_options_6131_, v___x_6139_);
                        v___y_6120_ = v_fileMap_6130_;
                        v___y_6121_ = v_fileName_6129_;
                        v___y_6122_ = v_suppressElabErrors_6133_;
                        v___y_6123_ = v___f_6136_;
                        v___y_6124_ = v_ref_6132_;
                        v___y_6125_ = v___y_6128_;
                        v___y_6126_ = v___x_6140_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_6028_);
                    v___x_6141_ = leanh::lean_box(0);
                    v___x_6142_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6142_, 0, v___x_6141_);
                    return v___x_6142_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(
    mut v_ref_6145_: *mut leanh::LeanObject,
    mut v_msgData_6146_: *mut leanh::LeanObject,
    mut v_severity_6147_: *mut leanh::LeanObject,
    mut v_isSilent_6148_: *mut leanh::LeanObject,
    mut v___y_6149_: *mut leanh::LeanObject,
    mut v___y_6150_: *mut leanh::LeanObject,
    mut v___y_6151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_6152_: u8 = 0;
    let mut v_isSilent_boxed_6153_: u8 = 0;
    let mut v_res_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6152_ = (leanh::lean_unbox(v_severity_6147_) as u8);
    v_isSilent_boxed_6153_ = (leanh::lean_unbox(v_isSilent_6148_) as u8);
    v_res_6154_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_6145_, v_msgData_6146_, v_severity_boxed_6152_, v_isSilent_boxed_6153_, v___y_6149_, v___y_6150_);
    leanh::lean_dec(v___y_6150_);
    leanh::lean_dec_ref(v___y_6149_);
    leanh::lean_dec(v_ref_6145_);
    return v_res_6154_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(
    mut v_msgData_6155_: *mut leanh::LeanObject,
    mut v_severity_6156_: u8,
    mut v_isSilent_6157_: u8,
    mut v___y_6158_: *mut leanh::LeanObject,
    mut v___y_6159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_6161_ = leanh::lean_ctor_get(v___y_6158_, 5);
    v___x_6162_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_6161_, v_msgData_6155_, v_severity_6156_, v_isSilent_6157_, v___y_6158_, v___y_6159_);
    return v___x_6162_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(
    mut v_msgData_6163_: *mut leanh::LeanObject,
    mut v_severity_6164_: *mut leanh::LeanObject,
    mut v_isSilent_6165_: *mut leanh::LeanObject,
    mut v___y_6166_: *mut leanh::LeanObject,
    mut v___y_6167_: *mut leanh::LeanObject,
    mut v___y_6168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_6169_: u8 = 0;
    let mut v_isSilent_boxed_6170_: u8 = 0;
    let mut v_res_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6169_ = (leanh::lean_unbox(v_severity_6164_) as u8);
    v_isSilent_boxed_6170_ = (leanh::lean_unbox(v_isSilent_6165_) as u8);
    v_res_6171_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(
        v_msgData_6163_,
        v_severity_boxed_6169_,
        v_isSilent_boxed_6170_,
        v___y_6166_,
        v___y_6167_,
    );
    leanh::lean_dec(v___y_6167_);
    leanh::lean_dec_ref(v___y_6166_);
    return v_res_6171_;
}
pub unsafe fn l_Lean_logError___at___00main_spec__14(
    mut v_msgData_6172_: *mut leanh::LeanObject,
    mut v___y_6173_: *mut leanh::LeanObject,
    mut v___y_6174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6176_: u8 = 0;
    let mut v___x_6177_: u8 = 0;
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6176_ = 2;
    v___x_6177_ = 0;
    v___x_6178_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(
        v_msgData_6172_,
        v___x_6176_,
        v___x_6177_,
        v___y_6173_,
        v___y_6174_,
    );
    return v___x_6178_;
}
pub unsafe fn l_Lean_logError___at___00main_spec__14___boxed(
    mut v_msgData_6179_: *mut leanh::LeanObject,
    mut v___y_6180_: *mut leanh::LeanObject,
    mut v___y_6181_: *mut leanh::LeanObject,
    mut v___y_6182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6183_ = l_Lean_logError___at___00main_spec__14(v_msgData_6179_, v___y_6180_, v___y_6181_);
    leanh::lean_dec(v___y_6181_);
    leanh::lean_dec_ref(v___y_6180_);
    return v_res_6183_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(
    mut v_x2_6184_: *mut leanh::LeanObject,
    mut v_as_6185_: *mut leanh::LeanObject,
    mut v_i_6186_: usize,
    mut v_stop_6187_: usize,
    mut v_b_6188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6189_: u8 = 0;
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: usize = 0;
    let mut v___x_6193_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6189_ = lean_usize_dec_eq(v_i_6186_, v_stop_6187_);
                if v___x_6189_ == 0 {
                    v___x_6190_ = lean_array_uget_borrowed(v_as_6185_, v_i_6186_);
                    leanh::lean_inc_ref(v_x2_6184_);
                    leanh::lean_inc(v___x_6190_);
                    v___x_6191_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_6190_, v_x2_6184_, v_b_6188_);
                    v___x_6192_ = 1usize;
                    v___x_6193_ = lean_usize_add(v_i_6186_, v___x_6192_);
                    v_i_6186_ = v___x_6193_;
                    v_b_6188_ = v___x_6191_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_x2_6184_);
                    return v_b_6188_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(
    mut v_x2_6195_: *mut leanh::LeanObject,
    mut v_as_6196_: *mut leanh::LeanObject,
    mut v_i_6197_: *mut leanh::LeanObject,
    mut v_stop_6198_: *mut leanh::LeanObject,
    mut v_b_6199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6200_: usize = 0;
    let mut v_stop_boxed_6201_: usize = 0;
    let mut v_res_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6200_ = leanh::lean_unbox_usize(v_i_6197_);
    leanh::lean_dec(v_i_6197_);
    v_stop_boxed_6201_ = leanh::lean_unbox_usize(v_stop_6198_);
    leanh::lean_dec(v_stop_6198_);
    v_res_6202_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(
            v_x2_6195_,
            v_as_6196_,
            v_i_boxed_6200_,
            v_stop_boxed_6201_,
            v_b_6199_,
        );
    leanh::lean_dec_ref(v_as_6196_);
    return v_res_6202_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(
    mut v_as_6203_: *mut leanh::LeanObject,
    mut v_i_6204_: usize,
    mut v_stop_6205_: usize,
    mut v_b_6206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: usize = 0;
    let mut v___x_6210_: usize = 0;
    let mut v___x_6212_: u8 = 0;
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declNames_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: u8 = 0;
    let mut v___x_6218_: u8 = 0;
    let mut v___x_6219_: usize = 0;
    let mut v___x_6220_: usize = 0;
    let mut v___x_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: usize = 0;
    let mut v___x_6223_: usize = 0;
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6212_ = lean_usize_dec_eq(v_i_6204_, v_stop_6205_);
                if v___x_6212_ == 0 {
                    v___x_6213_ = lean_array_uget_borrowed(v_as_6203_, v_i_6204_);
                    v_declNames_6214_ = leanh::lean_ctor_get(v___x_6213_, 0);
                    v___x_6215_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6216_ = lean_array_get_size(v_declNames_6214_);
                    v___x_6217_ = lean_nat_dec_lt(v___x_6215_, v___x_6216_);
                    if v___x_6217_ == 0 {
                        v___y_6208_ = v_b_6206_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6218_ = lean_nat_dec_le(v___x_6216_, v___x_6216_);
                        if v___x_6218_ == 0 {
                            if v___x_6217_ == 0 {
                                v___y_6208_ = v_b_6206_;
                                state = 1;
                                continue;
                            } else {
                                v___x_6219_ = 0usize;
                                v___x_6220_ = lean_usize_of_nat(v___x_6216_);
                                leanh::lean_inc(v___x_6213_);
                                v___x_6221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_6213_, v_declNames_6214_, v___x_6219_, v___x_6220_, v_b_6206_);
                                v___y_6208_ = v___x_6221_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_6222_ = 0usize;
                            v___x_6223_ = lean_usize_of_nat(v___x_6216_);
                            leanh::lean_inc(v___x_6213_);
                            v___x_6224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_6213_, v_declNames_6214_, v___x_6222_, v___x_6223_, v_b_6206_);
                            v___y_6208_ = v___x_6224_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_6206_;
                }
            }
            1 => {
                v___x_6209_ = 1usize;
                v___x_6210_ = lean_usize_add(v_i_6204_, v___x_6209_);
                v_i_6204_ = v___x_6210_;
                v_b_6206_ = v___y_6208_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(
    mut v_as_6225_: *mut leanh::LeanObject,
    mut v_i_6226_: *mut leanh::LeanObject,
    mut v_stop_6227_: *mut leanh::LeanObject,
    mut v_b_6228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6229_: usize = 0;
    let mut v_stop_boxed_6230_: usize = 0;
    let mut v_res_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6229_ = leanh::lean_unbox_usize(v_i_6226_);
    leanh::lean_dec(v_i_6226_);
    v_stop_boxed_6230_ = leanh::lean_unbox_usize(v_stop_6227_);
    leanh::lean_dec(v_stop_6227_);
    v_res_6231_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(
            v_as_6225_,
            v_i_boxed_6229_,
            v_stop_boxed_6230_,
            v_b_6228_,
        );
    leanh::lean_dec_ref(v_as_6225_);
    return v_res_6231_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(
    mut v_a_6232_: *mut leanh::LeanObject,
    mut v_as_6233_: *mut leanh::LeanObject,
    mut v_i_6234_: usize,
    mut v_stop_6235_: usize,
    mut v_b_6236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: usize = 0;
    let mut v___x_6240_: usize = 0;
    let mut v___x_6242_: u8 = 0;
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: u8 = 0;
    let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6242_ = lean_usize_dec_eq(v_i_6234_, v_stop_6235_);
                if v___x_6242_ == 0 {
                    v___x_6243_ = lean_array_uget_borrowed(v_as_6233_, v_i_6234_);
                    v_name_6244_ = leanh::lean_ctor_get(v___x_6243_, 0);
                    leanh::lean_inc(v_name_6244_);
                    leanh::lean_inc_ref(v_a_6232_);
                    v___x_6245_ = l_Lean_isExtern(v_a_6232_, v_name_6244_);
                    if v___x_6245_ == 0 {
                        v___y_6238_ = v_b_6236_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_6243_);
                        v___x_6246_ = lean_array_push(v_b_6236_, v___x_6243_);
                        v___y_6238_ = v___x_6246_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_6232_);
                    return v_b_6236_;
                }
            }
            1 => {
                v___x_6239_ = 1usize;
                v___x_6240_ = lean_usize_add(v_i_6234_, v___x_6239_);
                v_i_6234_ = v___x_6240_;
                v_b_6236_ = v___y_6238_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(
    mut v_a_6247_: *mut leanh::LeanObject,
    mut v_as_6248_: *mut leanh::LeanObject,
    mut v_i_6249_: *mut leanh::LeanObject,
    mut v_stop_6250_: *mut leanh::LeanObject,
    mut v_b_6251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6252_: usize = 0;
    let mut v_stop_boxed_6253_: usize = 0;
    let mut v_res_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6252_ = leanh::lean_unbox_usize(v_i_6249_);
    leanh::lean_dec(v_i_6249_);
    v_stop_boxed_6253_ = leanh::lean_unbox_usize(v_stop_6250_);
    leanh::lean_dec(v_stop_6250_);
    v_res_6254_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(
            v_a_6247_,
            v_as_6248_,
            v_i_boxed_6252_,
            v_stop_boxed_6253_,
            v_b_6251_,
        );
    leanh::lean_dec_ref(v_as_6248_);
    return v_res_6254_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(
    mut v_as_6255_: *mut leanh::LeanObject,
    mut v_sz_6256_: usize,
    mut v_i_6257_: usize,
    mut v_b_6258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6260_: u8 = 0;
    let mut v___x_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: u8 = 0;
    let mut v_a_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: usize = 0;
    let mut v___x_6268_: usize = 0;
    let mut v_a_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6273_: u8 = 0;
    let mut v___x_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6260_ = lean_usize_dec_lt(v_i_6257_, v_sz_6256_);
                if v___x_6260_ == 0 {
                    v___x_6261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6261_, 0, v_b_6258_);
                    return v___x_6261_;
                } else {
                    leanh::lean_dec_ref(v_b_6258_);
                    v___x_6262_ = 0;
                    v_a_6263_ = lean_array_uget_borrowed(v_as_6255_, v_i_6257_);
                    leanh::lean_inc(v_a_6263_);
                    v___x_6264_ = l_Lean_Message_toString(v_a_6263_, v___x_6262_);
                    v___x_6265_ = l_IO_eprintln___at___00main_spec__6(v___x_6264_);
                    if leanh::lean_obj_tag(v___x_6265_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6265_, 1);
                        v___x_6266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0;
                        v___x_6267_ = 1usize;
                        v___x_6268_ = lean_usize_add(v_i_6257_, v___x_6267_);
                        v_i_6257_ = v___x_6268_;
                        v_b_6258_ = v___x_6266_;
                        state = 0;
                        continue;
                    } else {
                        v_a_6270_ = leanh::lean_ctor_get(v___x_6265_, 0);
                        v_isSharedCheck_6277_ =
                            (!leanh::lean_is_exclusive(v___x_6265_)) as u8;
                        if v_isSharedCheck_6277_ == 0 {
                            v___x_6272_ = v___x_6265_;
                            v_isShared_6273_ = v_isSharedCheck_6277_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6270_);
                            leanh::lean_dec(v___x_6265_);
                            v___x_6272_ = leanh::lean_box(0);
                            v_isShared_6273_ = v_isSharedCheck_6277_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6273_ == 0 {
                    v___x_6275_ = v___x_6272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_a_6270_);
                    v___x_6275_ = v_reuseFailAlloc_6276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(
    mut v_as_6278_: *mut leanh::LeanObject,
    mut v_sz_6279_: *mut leanh::LeanObject,
    mut v_i_6280_: *mut leanh::LeanObject,
    mut v_b_6281_: *mut leanh::LeanObject,
    mut v___y_6282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6283_: usize = 0;
    let mut v_i_boxed_6284_: usize = 0;
    let mut v_res_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6283_ = leanh::lean_unbox_usize(v_sz_6279_);
    leanh::lean_dec(v_sz_6279_);
    v_i_boxed_6284_ = leanh::lean_unbox_usize(v_i_6280_);
    leanh::lean_dec(v_i_6280_);
    v_res_6285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_6278_, v_sz_boxed_6283_, v_i_boxed_6284_, v_b_6281_);
    leanh::lean_dec_ref(v_as_6278_);
    return v_res_6285_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(
    mut v_as_6286_: *mut leanh::LeanObject,
    mut v_sz_6287_: usize,
    mut v_i_6288_: usize,
    mut v_b_6289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6291_: u8 = 0;
    let mut v___x_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: u8 = 0;
    let mut v_a_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: usize = 0;
    let mut v___x_6299_: usize = 0;
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6304_: u8 = 0;
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6291_ = lean_usize_dec_lt(v_i_6288_, v_sz_6287_);
                if v___x_6291_ == 0 {
                    v___x_6292_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6292_, 0, v_b_6289_);
                    return v___x_6292_;
                } else {
                    leanh::lean_dec_ref(v_b_6289_);
                    v___x_6293_ = 0;
                    v_a_6294_ = lean_array_uget_borrowed(v_as_6286_, v_i_6288_);
                    leanh::lean_inc(v_a_6294_);
                    v___x_6295_ = l_Lean_Message_toString(v_a_6294_, v___x_6293_);
                    v___x_6296_ = l_IO_eprintln___at___00main_spec__6(v___x_6295_);
                    if leanh::lean_obj_tag(v___x_6296_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6296_, 1);
                        v___x_6297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0;
                        v___x_6298_ = 1usize;
                        v___x_6299_ = lean_usize_add(v_i_6288_, v___x_6298_);
                        v___x_6300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_6286_, v_sz_6287_, v___x_6299_, v___x_6297_);
                        return v___x_6300_;
                    } else {
                        v_a_6301_ = leanh::lean_ctor_get(v___x_6296_, 0);
                        v_isSharedCheck_6308_ =
                            (!leanh::lean_is_exclusive(v___x_6296_)) as u8;
                        if v_isSharedCheck_6308_ == 0 {
                            v___x_6303_ = v___x_6296_;
                            v_isShared_6304_ = v_isSharedCheck_6308_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6301_);
                            leanh::lean_dec(v___x_6296_);
                            v___x_6303_ = leanh::lean_box(0);
                            v_isShared_6304_ = v_isSharedCheck_6308_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6304_ == 0 {
                    v___x_6306_ = v___x_6303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6307_, 0, v_a_6301_);
                    v___x_6306_ = v_reuseFailAlloc_6307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(
    mut v_as_6309_: *mut leanh::LeanObject,
    mut v_sz_6310_: *mut leanh::LeanObject,
    mut v_i_6311_: *mut leanh::LeanObject,
    mut v_b_6312_: *mut leanh::LeanObject,
    mut v___y_6313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6314_: usize = 0;
    let mut v_i_boxed_6315_: usize = 0;
    let mut v_res_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6314_ = leanh::lean_unbox_usize(v_sz_6310_);
    leanh::lean_dec(v_sz_6310_);
    v_i_boxed_6315_ = leanh::lean_unbox_usize(v_i_6311_);
    leanh::lean_dec(v_i_6311_);
    v_res_6316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_6309_, v_sz_boxed_6314_, v_i_boxed_6315_, v_b_6312_);
    leanh::lean_dec_ref(v_as_6309_);
    return v_res_6316_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(
    mut v_init_6317_: *mut leanh::LeanObject,
    mut v_n_6318_: *mut leanh::LeanObject,
    mut v_b_6319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6324_: usize = 0;
    let mut v___x_6325_: usize = 0;
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6330_: u8 = 0;
    let mut v_fst_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6341_: u8 = 0;
    let mut v_a_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6345_: u8 = 0;
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6349_: u8 = 0;
    let mut v_vs_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6353_: usize = 0;
    let mut v___x_6354_: usize = 0;
    let mut v___x_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v_fst_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6370_: u8 = 0;
    let mut v_a_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6374_: u8 = 0;
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_6318_) == 0 {
                    v_cs_6321_ = leanh::lean_ctor_get(v_n_6318_, 0);
                    v___x_6322_ = leanh::lean_box(0);
                    v___x_6323_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6323_, 0, v___x_6322_);
                    leanh::lean_ctor_set(v___x_6323_, 1, v_b_6319_);
                    v_sz_6324_ = lean_array_size(v_cs_6321_);
                    v___x_6325_ = 0usize;
                    v___x_6326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_6317_, v_cs_6321_, v_sz_6324_, v___x_6325_, v___x_6323_);
                    if leanh::lean_obj_tag(v___x_6326_) == 0 {
                        v_a_6327_ = leanh::lean_ctor_get(v___x_6326_, 0);
                        v_isSharedCheck_6341_ =
                            (!leanh::lean_is_exclusive(v___x_6326_)) as u8;
                        if v_isSharedCheck_6341_ == 0 {
                            v___x_6329_ = v___x_6326_;
                            v_isShared_6330_ = v_isSharedCheck_6341_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6327_);
                            leanh::lean_dec(v___x_6326_);
                            v___x_6329_ = leanh::lean_box(0);
                            v_isShared_6330_ = v_isSharedCheck_6341_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6342_ = leanh::lean_ctor_get(v___x_6326_, 0);
                        v_isSharedCheck_6349_ =
                            (!leanh::lean_is_exclusive(v___x_6326_)) as u8;
                        if v_isSharedCheck_6349_ == 0 {
                            v___x_6344_ = v___x_6326_;
                            v_isShared_6345_ = v_isSharedCheck_6349_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6342_);
                            leanh::lean_dec(v___x_6326_);
                            v___x_6344_ = leanh::lean_box(0);
                            v_isShared_6345_ = v_isSharedCheck_6349_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6350_ = leanh::lean_ctor_get(v_n_6318_, 0);
                    v___x_6351_ = leanh::lean_box(0);
                    v___x_6352_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6352_, 0, v___x_6351_);
                    leanh::lean_ctor_set(v___x_6352_, 1, v_b_6319_);
                    v_sz_6353_ = lean_array_size(v_vs_6350_);
                    v___x_6354_ = 0usize;
                    v___x_6355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_6350_, v_sz_6353_, v___x_6354_, v___x_6352_);
                    if leanh::lean_obj_tag(v___x_6355_) == 0 {
                        v_a_6356_ = leanh::lean_ctor_get(v___x_6355_, 0);
                        v_isSharedCheck_6370_ =
                            (!leanh::lean_is_exclusive(v___x_6355_)) as u8;
                        if v_isSharedCheck_6370_ == 0 {
                            v___x_6358_ = v___x_6355_;
                            v_isShared_6359_ = v_isSharedCheck_6370_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6356_);
                            leanh::lean_dec(v___x_6355_);
                            v___x_6358_ = leanh::lean_box(0);
                            v_isShared_6359_ = v_isSharedCheck_6370_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6371_ = leanh::lean_ctor_get(v___x_6355_, 0);
                        v_isSharedCheck_6378_ =
                            (!leanh::lean_is_exclusive(v___x_6355_)) as u8;
                        if v_isSharedCheck_6378_ == 0 {
                            v___x_6373_ = v___x_6355_;
                            v_isShared_6374_ = v_isSharedCheck_6378_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6371_);
                            leanh::lean_dec(v___x_6355_);
                            v___x_6373_ = leanh::lean_box(0);
                            v_isShared_6374_ = v_isSharedCheck_6378_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6331_ = leanh::lean_ctor_get(v_a_6327_, 0);
                if leanh::lean_obj_tag(v_fst_6331_) == 0 {
                    v_snd_6332_ = leanh::lean_ctor_get(v_a_6327_, 1);
                    leanh::lean_inc(v_snd_6332_);
                    leanh::lean_dec(v_a_6327_);
                    v___x_6333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6333_, 0, v_snd_6332_);
                    if v_isShared_6330_ == 0 {
                        leanh::lean_ctor_set(v___x_6329_, 0, v___x_6333_);
                        v___x_6335_ = v___x_6329_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6336_, 0, v___x_6333_);
                        v___x_6335_ = v_reuseFailAlloc_6336_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6331_);
                    leanh::lean_dec(v_a_6327_);
                    v_val_6337_ = leanh::lean_ctor_get(v_fst_6331_, 0);
                    leanh::lean_inc(v_val_6337_);
                    leanh::lean_dec_ref_known(v_fst_6331_, 1);
                    if v_isShared_6330_ == 0 {
                        leanh::lean_ctor_set(v___x_6329_, 0, v_val_6337_);
                        v___x_6339_ = v___x_6329_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6340_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 0, v_val_6337_);
                        v___x_6339_ = v_reuseFailAlloc_6340_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6335_;
            }
            3 => {
                return v___x_6339_;
            }
            4 => {
                if v_isShared_6345_ == 0 {
                    v___x_6347_ = v___x_6344_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6348_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6348_, 0, v_a_6342_);
                    v___x_6347_ = v_reuseFailAlloc_6348_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6347_;
            }
            6 => {
                v_fst_6360_ = leanh::lean_ctor_get(v_a_6356_, 0);
                if leanh::lean_obj_tag(v_fst_6360_) == 0 {
                    v_snd_6361_ = leanh::lean_ctor_get(v_a_6356_, 1);
                    leanh::lean_inc(v_snd_6361_);
                    leanh::lean_dec(v_a_6356_);
                    v___x_6362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6362_, 0, v_snd_6361_);
                    if v_isShared_6359_ == 0 {
                        leanh::lean_ctor_set(v___x_6358_, 0, v___x_6362_);
                        v___x_6364_ = v___x_6358_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6365_, 0, v___x_6362_);
                        v___x_6364_ = v_reuseFailAlloc_6365_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6360_);
                    leanh::lean_dec(v_a_6356_);
                    v_val_6366_ = leanh::lean_ctor_get(v_fst_6360_, 0);
                    leanh::lean_inc(v_val_6366_);
                    leanh::lean_dec_ref_known(v_fst_6360_, 1);
                    if v_isShared_6359_ == 0 {
                        leanh::lean_ctor_set(v___x_6358_, 0, v_val_6366_);
                        v___x_6368_ = v___x_6358_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6369_, 0, v_val_6366_);
                        v___x_6368_ = v_reuseFailAlloc_6369_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6364_;
            }
            8 => {
                return v___x_6368_;
            }
            9 => {
                if v_isShared_6374_ == 0 {
                    v___x_6376_ = v___x_6373_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6377_, 0, v_a_6371_);
                    v___x_6376_ = v_reuseFailAlloc_6377_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(
    mut v_init_6379_: *mut leanh::LeanObject,
    mut v_as_6380_: *mut leanh::LeanObject,
    mut v_sz_6381_: usize,
    mut v_i_6382_: usize,
    mut v_b_6383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6385_: u8 = 0;
    let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6390_: u8 = 0;
    let mut v_a_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6396_: u8 = 0;
    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: usize = 0;
    let mut v___x_6409_: usize = 0;
    let mut v_reuseFailAlloc_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6412_: u8 = 0;
    let mut v_a_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6416_: u8 = 0;
    let mut v___x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6420_: u8 = 0;
    let mut v_isSharedCheck_6421_: u8 = 0;
    let mut v_unused_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6385_ = lean_usize_dec_lt(v_i_6382_, v_sz_6381_);
                if v___x_6385_ == 0 {
                    v___x_6386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6386_, 0, v_b_6383_);
                    return v___x_6386_;
                } else {
                    v_snd_6387_ = leanh::lean_ctor_get(v_b_6383_, 1);
                    v_isSharedCheck_6421_ = (!leanh::lean_is_exclusive(v_b_6383_)) as u8;
                    if v_isSharedCheck_6421_ == 0 {
                        v_unused_6422_ = leanh::lean_ctor_get(v_b_6383_, 0);
                        leanh::lean_dec(v_unused_6422_);
                        v___x_6389_ = v_b_6383_;
                        v_isShared_6390_ = v_isSharedCheck_6421_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6387_);
                        leanh::lean_dec(v_b_6383_);
                        v___x_6389_ = leanh::lean_box(0);
                        v_isShared_6390_ = v_isSharedCheck_6421_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6391_ = lean_array_uget_borrowed(v_as_6380_, v_i_6382_);
                leanh::lean_inc(v_snd_6387_);
                v___x_6392_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_6379_, v_a_6391_, v_snd_6387_);
                if leanh::lean_obj_tag(v___x_6392_) == 0 {
                    v_a_6393_ = leanh::lean_ctor_get(v___x_6392_, 0);
                    v_isSharedCheck_6412_ = (!leanh::lean_is_exclusive(v___x_6392_)) as u8;
                    if v_isSharedCheck_6412_ == 0 {
                        v___x_6395_ = v___x_6392_;
                        v_isShared_6396_ = v_isSharedCheck_6412_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6393_);
                        leanh::lean_dec(v___x_6392_);
                        v___x_6395_ = leanh::lean_box(0);
                        v_isShared_6396_ = v_isSharedCheck_6412_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6389_);
                    leanh::lean_dec(v_snd_6387_);
                    v_a_6413_ = leanh::lean_ctor_get(v___x_6392_, 0);
                    v_isSharedCheck_6420_ = (!leanh::lean_is_exclusive(v___x_6392_)) as u8;
                    if v_isSharedCheck_6420_ == 0 {
                        v___x_6415_ = v___x_6392_;
                        v_isShared_6416_ = v_isSharedCheck_6420_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6413_);
                        leanh::lean_dec(v___x_6392_);
                        v___x_6415_ = leanh::lean_box(0);
                        v_isShared_6416_ = v_isSharedCheck_6420_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_6393_) == 0 {
                    v___x_6397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6397_, 0, v_a_6393_);
                    if v_isShared_6390_ == 0 {
                        leanh::lean_ctor_set(v___x_6389_, 0, v___x_6397_);
                        v___x_6399_ = v___x_6389_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6403_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6403_, 0, v___x_6397_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6403_, 1, v_snd_6387_);
                        v___x_6399_ = v_reuseFailAlloc_6403_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6395_);
                    leanh::lean_dec(v_snd_6387_);
                    v_a_6404_ = leanh::lean_ctor_get(v_a_6393_, 0);
                    leanh::lean_inc(v_a_6404_);
                    leanh::lean_dec_ref_known(v_a_6393_, 1);
                    v___x_6405_ = leanh::lean_box(0);
                    if v_isShared_6390_ == 0 {
                        leanh::lean_ctor_set(v___x_6389_, 1, v_a_6404_);
                        leanh::lean_ctor_set(v___x_6389_, 0, v___x_6405_);
                        v___x_6407_ = v___x_6389_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6411_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 0, v___x_6405_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 1, v_a_6404_);
                        v___x_6407_ = v_reuseFailAlloc_6411_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6396_ == 0 {
                    leanh::lean_ctor_set(v___x_6395_, 0, v___x_6399_);
                    v___x_6401_ = v___x_6395_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6402_, 0, v___x_6399_);
                    v___x_6401_ = v_reuseFailAlloc_6402_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6401_;
            }
            5 => {
                v___x_6408_ = 1usize;
                v___x_6409_ = lean_usize_add(v_i_6382_, v___x_6408_);
                v_i_6382_ = v___x_6409_;
                v_b_6383_ = v___x_6407_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6416_ == 0 {
                    v___x_6418_ = v___x_6415_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_a_6413_);
                    v___x_6418_ = v_reuseFailAlloc_6419_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(
    mut v_init_6423_: *mut leanh::LeanObject,
    mut v_as_6424_: *mut leanh::LeanObject,
    mut v_sz_6425_: *mut leanh::LeanObject,
    mut v_i_6426_: *mut leanh::LeanObject,
    mut v_b_6427_: *mut leanh::LeanObject,
    mut v___y_6428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6429_: usize = 0;
    let mut v_i_boxed_6430_: usize = 0;
    let mut v_res_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6429_ = leanh::lean_unbox_usize(v_sz_6425_);
    leanh::lean_dec(v_sz_6425_);
    v_i_boxed_6430_ = leanh::lean_unbox_usize(v_i_6426_);
    leanh::lean_dec(v_i_6426_);
    v_res_6431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_6423_, v_as_6424_, v_sz_boxed_6429_, v_i_boxed_6430_, v_b_6427_);
    leanh::lean_dec_ref(v_as_6424_);
    return v_res_6431_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(
    mut v_init_6432_: *mut leanh::LeanObject,
    mut v_n_6433_: *mut leanh::LeanObject,
    mut v_b_6434_: *mut leanh::LeanObject,
    mut v___y_6435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6436_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_6432_, v_n_6433_, v_b_6434_);
    leanh::lean_dec_ref(v_n_6433_);
    return v_res_6436_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(
    mut v_as_6437_: *mut leanh::LeanObject,
    mut v_sz_6438_: usize,
    mut v_i_6439_: usize,
    mut v_b_6440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6442_: u8 = 0;
    let mut v___x_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: u8 = 0;
    let mut v_a_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: usize = 0;
    let mut v___x_6450_: usize = 0;
    let mut v_a_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6455_: u8 = 0;
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6442_ = lean_usize_dec_lt(v_i_6439_, v_sz_6438_);
                if v___x_6442_ == 0 {
                    v___x_6443_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6443_, 0, v_b_6440_);
                    return v___x_6443_;
                } else {
                    leanh::lean_dec_ref(v_b_6440_);
                    v___x_6444_ = 0;
                    v_a_6445_ = lean_array_uget_borrowed(v_as_6437_, v_i_6439_);
                    leanh::lean_inc(v_a_6445_);
                    v___x_6446_ = l_Lean_Message_toString(v_a_6445_, v___x_6444_);
                    v___x_6447_ = l_IO_eprintln___at___00main_spec__6(v___x_6446_);
                    if leanh::lean_obj_tag(v___x_6447_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6447_, 1);
                        v___x_6448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0;
                        v___x_6449_ = 1usize;
                        v___x_6450_ = lean_usize_add(v_i_6439_, v___x_6449_);
                        v_i_6439_ = v___x_6450_;
                        v_b_6440_ = v___x_6448_;
                        state = 0;
                        continue;
                    } else {
                        v_a_6452_ = leanh::lean_ctor_get(v___x_6447_, 0);
                        v_isSharedCheck_6459_ =
                            (!leanh::lean_is_exclusive(v___x_6447_)) as u8;
                        if v_isSharedCheck_6459_ == 0 {
                            v___x_6454_ = v___x_6447_;
                            v_isShared_6455_ = v_isSharedCheck_6459_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6452_);
                            leanh::lean_dec(v___x_6447_);
                            v___x_6454_ = leanh::lean_box(0);
                            v_isShared_6455_ = v_isSharedCheck_6459_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6455_ == 0 {
                    v___x_6457_ = v___x_6454_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6458_, 0, v_a_6452_);
                    v___x_6457_ = v_reuseFailAlloc_6458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(
    mut v_as_6460_: *mut leanh::LeanObject,
    mut v_sz_6461_: *mut leanh::LeanObject,
    mut v_i_6462_: *mut leanh::LeanObject,
    mut v_b_6463_: *mut leanh::LeanObject,
    mut v___y_6464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6465_: usize = 0;
    let mut v_i_boxed_6466_: usize = 0;
    let mut v_res_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6465_ = leanh::lean_unbox_usize(v_sz_6461_);
    leanh::lean_dec(v_sz_6461_);
    v_i_boxed_6466_ = leanh::lean_unbox_usize(v_i_6462_);
    leanh::lean_dec(v_i_6462_);
    v_res_6467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_6460_, v_sz_boxed_6465_, v_i_boxed_6466_, v_b_6463_);
    leanh::lean_dec_ref(v_as_6460_);
    return v_res_6467_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(
    mut v_as_6468_: *mut leanh::LeanObject,
    mut v_sz_6469_: usize,
    mut v_i_6470_: usize,
    mut v_b_6471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6473_: u8 = 0;
    let mut v___x_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: u8 = 0;
    let mut v_a_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: usize = 0;
    let mut v___x_6481_: usize = 0;
    let mut v___x_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6486_: u8 = 0;
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6473_ = lean_usize_dec_lt(v_i_6470_, v_sz_6469_);
                if v___x_6473_ == 0 {
                    v___x_6474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6474_, 0, v_b_6471_);
                    return v___x_6474_;
                } else {
                    leanh::lean_dec_ref(v_b_6471_);
                    v___x_6475_ = 0;
                    v_a_6476_ = lean_array_uget_borrowed(v_as_6468_, v_i_6470_);
                    leanh::lean_inc(v_a_6476_);
                    v___x_6477_ = l_Lean_Message_toString(v_a_6476_, v___x_6475_);
                    v___x_6478_ = l_IO_eprintln___at___00main_spec__6(v___x_6477_);
                    if leanh::lean_obj_tag(v___x_6478_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6478_, 1);
                        v___x_6479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0;
                        v___x_6480_ = 1usize;
                        v___x_6481_ = lean_usize_add(v_i_6470_, v___x_6480_);
                        v___x_6482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_6468_, v_sz_6469_, v___x_6481_, v___x_6479_);
                        return v___x_6482_;
                    } else {
                        v_a_6483_ = leanh::lean_ctor_get(v___x_6478_, 0);
                        v_isSharedCheck_6490_ =
                            (!leanh::lean_is_exclusive(v___x_6478_)) as u8;
                        if v_isSharedCheck_6490_ == 0 {
                            v___x_6485_ = v___x_6478_;
                            v_isShared_6486_ = v_isSharedCheck_6490_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6483_);
                            leanh::lean_dec(v___x_6478_);
                            v___x_6485_ = leanh::lean_box(0);
                            v_isShared_6486_ = v_isSharedCheck_6490_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6486_ == 0 {
                    v___x_6488_ = v___x_6485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 0, v_a_6483_);
                    v___x_6488_ = v_reuseFailAlloc_6489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(
    mut v_as_6491_: *mut leanh::LeanObject,
    mut v_sz_6492_: *mut leanh::LeanObject,
    mut v_i_6493_: *mut leanh::LeanObject,
    mut v_b_6494_: *mut leanh::LeanObject,
    mut v___y_6495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6496_: usize = 0;
    let mut v_i_boxed_6497_: usize = 0;
    let mut v_res_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6496_ = leanh::lean_unbox_usize(v_sz_6492_);
    leanh::lean_dec(v_sz_6492_);
    v_i_boxed_6497_ = leanh::lean_unbox_usize(v_i_6493_);
    leanh::lean_dec(v_i_6493_);
    v_res_6498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_6491_, v_sz_boxed_6496_, v_i_boxed_6497_, v_b_6494_);
    leanh::lean_dec_ref(v_as_6491_);
    return v_res_6498_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00main_spec__7(
    mut v_t_6499_: *mut leanh::LeanObject,
    mut v_init_6500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6508_: u8 = 0;
    let mut v_a_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6516_: usize = 0;
    let mut v___x_6517_: usize = 0;
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6522_: u8 = 0;
    let mut v_fst_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6532_: u8 = 0;
    let mut v_a_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6536_: u8 = 0;
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6540_: u8 = 0;
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v_a_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6545_: u8 = 0;
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6502_ = leanh::lean_ctor_get(v_t_6499_, 0);
                v_tail_6503_ = leanh::lean_ctor_get(v_t_6499_, 1);
                v___x_6504_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_6500_, v_root_6502_, v_init_6500_);
                if leanh::lean_obj_tag(v___x_6504_) == 0 {
                    v_a_6505_ = leanh::lean_ctor_get(v___x_6504_, 0);
                    v_isSharedCheck_6541_ = (!leanh::lean_is_exclusive(v___x_6504_)) as u8;
                    if v_isSharedCheck_6541_ == 0 {
                        v___x_6507_ = v___x_6504_;
                        v_isShared_6508_ = v_isSharedCheck_6541_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6505_);
                        leanh::lean_dec(v___x_6504_);
                        v___x_6507_ = leanh::lean_box(0);
                        v_isShared_6508_ = v_isSharedCheck_6541_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6542_ = leanh::lean_ctor_get(v___x_6504_, 0);
                    v_isSharedCheck_6549_ = (!leanh::lean_is_exclusive(v___x_6504_)) as u8;
                    if v_isSharedCheck_6549_ == 0 {
                        v___x_6544_ = v___x_6504_;
                        v_isShared_6545_ = v_isSharedCheck_6549_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6542_);
                        leanh::lean_dec(v___x_6504_);
                        v___x_6544_ = leanh::lean_box(0);
                        v_isShared_6545_ = v_isSharedCheck_6549_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6505_) == 0 {
                    v_a_6509_ = leanh::lean_ctor_get(v_a_6505_, 0);
                    leanh::lean_inc(v_a_6509_);
                    leanh::lean_dec_ref_known(v_a_6505_, 1);
                    if v_isShared_6508_ == 0 {
                        leanh::lean_ctor_set(v___x_6507_, 0, v_a_6509_);
                        v___x_6511_ = v___x_6507_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6512_, 0, v_a_6509_);
                        v___x_6511_ = v_reuseFailAlloc_6512_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6507_);
                    v_a_6513_ = leanh::lean_ctor_get(v_a_6505_, 0);
                    leanh::lean_inc(v_a_6513_);
                    leanh::lean_dec_ref_known(v_a_6505_, 1);
                    v___x_6514_ = leanh::lean_box(0);
                    v___x_6515_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6515_, 0, v___x_6514_);
                    leanh::lean_ctor_set(v___x_6515_, 1, v_a_6513_);
                    v_sz_6516_ = lean_array_size(v_tail_6503_);
                    v___x_6517_ = 0usize;
                    v___x_6518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_6503_, v_sz_6516_, v___x_6517_, v___x_6515_);
                    if leanh::lean_obj_tag(v___x_6518_) == 0 {
                        v_a_6519_ = leanh::lean_ctor_get(v___x_6518_, 0);
                        v_isSharedCheck_6532_ =
                            (!leanh::lean_is_exclusive(v___x_6518_)) as u8;
                        if v_isSharedCheck_6532_ == 0 {
                            v___x_6521_ = v___x_6518_;
                            v_isShared_6522_ = v_isSharedCheck_6532_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6519_);
                            leanh::lean_dec(v___x_6518_);
                            v___x_6521_ = leanh::lean_box(0);
                            v_isShared_6522_ = v_isSharedCheck_6532_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6533_ = leanh::lean_ctor_get(v___x_6518_, 0);
                        v_isSharedCheck_6540_ =
                            (!leanh::lean_is_exclusive(v___x_6518_)) as u8;
                        if v_isSharedCheck_6540_ == 0 {
                            v___x_6535_ = v___x_6518_;
                            v_isShared_6536_ = v_isSharedCheck_6540_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6533_);
                            leanh::lean_dec(v___x_6518_);
                            v___x_6535_ = leanh::lean_box(0);
                            v_isShared_6536_ = v_isSharedCheck_6540_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6511_;
            }
            3 => {
                v_fst_6523_ = leanh::lean_ctor_get(v_a_6519_, 0);
                if leanh::lean_obj_tag(v_fst_6523_) == 0 {
                    v_snd_6524_ = leanh::lean_ctor_get(v_a_6519_, 1);
                    leanh::lean_inc(v_snd_6524_);
                    leanh::lean_dec(v_a_6519_);
                    if v_isShared_6522_ == 0 {
                        leanh::lean_ctor_set(v___x_6521_, 0, v_snd_6524_);
                        v___x_6526_ = v___x_6521_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_snd_6524_);
                        v___x_6526_ = v_reuseFailAlloc_6527_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6523_);
                    leanh::lean_dec(v_a_6519_);
                    v_val_6528_ = leanh::lean_ctor_get(v_fst_6523_, 0);
                    leanh::lean_inc(v_val_6528_);
                    leanh::lean_dec_ref_known(v_fst_6523_, 1);
                    if v_isShared_6522_ == 0 {
                        leanh::lean_ctor_set(v___x_6521_, 0, v_val_6528_);
                        v___x_6530_ = v___x_6521_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6531_, 0, v_val_6528_);
                        v___x_6530_ = v_reuseFailAlloc_6531_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6526_;
            }
            5 => {
                return v___x_6530_;
            }
            6 => {
                if v_isShared_6536_ == 0 {
                    v___x_6538_ = v___x_6535_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6539_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6539_, 0, v_a_6533_);
                    v___x_6538_ = v_reuseFailAlloc_6539_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6538_;
            }
            8 => {
                if v_isShared_6545_ == 0 {
                    v___x_6547_ = v___x_6544_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6548_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6548_, 0, v_a_6542_);
                    v___x_6547_ = v_reuseFailAlloc_6548_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(
    mut v_t_6550_: *mut leanh::LeanObject,
    mut v_init_6551_: *mut leanh::LeanObject,
    mut v___y_6552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6553_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_6550_, v_init_6551_);
    leanh::lean_dec_ref(v_t_6550_);
    return v_res_6553_;
}
pub unsafe fn _init_l_main___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6557_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6557_;
}
pub unsafe fn _init_l_main___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_Lean_instInhabitedClassState_default;
    v___x_6559_ = leanh::lean_box(0);
    v___x_6560_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6560_, 0, v___x_6559_);
    leanh::lean_ctor_set(v___x_6560_, 1, v___x_6558_);
    return v___x_6560_;
}
pub unsafe fn _init_l_main___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6561_ = l_Lean_Meta_Match_Extension_instInhabitedState;
    v___x_6562_ = leanh::lean_box(0);
    v___x_6563_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6563_, 0, v___x_6562_);
    leanh::lean_ctor_set(v___x_6563_, 1, v___x_6561_);
    return v___x_6563_;
}
pub unsafe fn _init_l_main___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6564_ = l_main___closed__2;
    v___x_6565_ = l_main___closed__1;
    v___x_6566_ = l_Lean_PersistentHashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6565_,
        v___x_6564_,
    );
    return v___x_6566_;
}
pub unsafe fn _init_l_main___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6567_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_main___closed__6),
        core::ptr::addr_of_mut!(l_main___closed__6_once),
        _init_l_main___closed__6,
    );
    v___x_6568_ = leanh::lean_box(0);
    v___x_6569_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6569_, 0, v___x_6568_);
    leanh::lean_ctor_set(v___x_6569_, 1, v___x_6567_);
    return v___x_6569_;
}
pub unsafe fn _init_l_main___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6570_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_main___closed__7),
        core::ptr::addr_of_mut!(l_main___closed__7_once),
        _init_l_main___closed__7,
    );
    v___x_6571_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_6570_);
    return v___x_6571_;
}
pub unsafe fn _init_l_main___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6572_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_6572_;
}
pub unsafe fn _init_l_main___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6580_ = l_Lean_Options_empty;
    v___x_6581_ = l_Lean_Core_getMaxHeartbeats(v___x_6580_);
    return v___x_6581_;
}
pub unsafe fn _init_l_main___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6586_ = l_main___closed__18;
    v___x_6587_ = leanh::lean_unsigned_to_nat(27);
    v___x_6588_ = leanh::lean_unsigned_to_nat(143);
    v___x_6589_ = l_main___closed__17;
    v___x_6590_ = l_main___closed__16;
    v___x_6591_ = l_mkPanicMessageWithDecl(
        v___x_6590_,
        v___x_6589_,
        v___x_6588_,
        v___x_6587_,
        v___x_6586_,
    );
    return v___x_6591_;
}
pub unsafe fn _init_l_main___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6593_ = l_main___closed__18;
    v___x_6594_ = leanh::lean_unsigned_to_nat(51);
    v___x_6595_ = leanh::lean_unsigned_to_nat(116);
    v___x_6596_ = l_main___closed__17;
    v___x_6597_ = l_main___closed__16;
    v___x_6598_ = l_mkPanicMessageWithDecl(
        v___x_6597_,
        v___x_6596_,
        v___x_6595_,
        v___x_6594_,
        v___x_6593_,
    );
    return v___x_6598_;
}
pub unsafe fn _init_l_main___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6599_ = leanh::lean_unsigned_to_nat(1);
    v___x_6600_ = l_Lean_firstFrontendMacroScope;
    v___x_6601_ = lean_nat_add(v___x_6600_, v___x_6599_);
    return v___x_6601_;
}
pub unsafe fn _init_l_main___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: u64 = 0;
    let mut v___x_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6608_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
    v___x_6609_ = 0u64;
    v___x_6610_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_6610_, 0, v___x_6608_);
    leanh::lean_ctor_set_uint64(
        v___x_6610_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_6609_,
    );
    return v___x_6610_;
}
pub unsafe fn _init_l_main___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6611_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6611_;
}
pub unsafe fn _init_l_main___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6612_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_main___closed__27),
        core::ptr::addr_of_mut!(l_main___closed__27_once),
        _init_l_main___closed__27,
    );
    v___x_6613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6613_, 0, v___x_6612_);
    return v___x_6613_;
}
pub unsafe fn _init_l_main___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6614_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_main___closed__28),
        core::ptr::addr_of_mut!(l_main___closed__28_once),
        _init_l_main___closed__28,
    );
    v___x_6615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6615_, 0, v___x_6614_);
    leanh::lean_ctor_set(v___x_6615_, 1, v___x_6614_);
    return v___x_6615_;
}
pub unsafe fn _init_l_main___closed__30() -> *mut leanh::LeanObject {
    let mut v___x_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6616_ = l_Lean_NameSet_empty;
    v___x_6617_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
    v___x_6618_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6618_, 0, v___x_6617_);
    leanh::lean_ctor_set(v___x_6618_, 1, v___x_6617_);
    leanh::lean_ctor_set(v___x_6618_, 2, v___x_6616_);
    return v___x_6618_;
}
pub unsafe fn _init_l_main___closed__31() -> *mut leanh::LeanObject {
    let mut v___x_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: u8 = 0;
    let mut v___x_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6619_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
    v___x_6620_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_main___closed__28),
        core::ptr::addr_of_mut!(l_main___closed__28_once),
        _init_l_main___closed__28,
    );
    v___x_6621_ = 1;
    v___x_6622_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_6622_, 0, v___x_6620_);
    leanh::lean_ctor_set(v___x_6622_, 1, v___x_6620_);
    leanh::lean_ctor_set(v___x_6622_, 2, v___x_6619_);
    leanh::lean_ctor_set_uint8(
        v___x_6622_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_6621_,
    );
    return v___x_6622_;
}
pub unsafe fn _init_l_main___closed__36() -> u8 {
    let mut v___x_6629_: u8 = 0;
    let mut v___x_6630_: u8 = 0;
    v___x_6629_ = 2;
    v___x_6630_ = l_Lean_instOrdOLeanLevel_ord(v___x_6629_, v___x_6629_);
    return v___x_6630_;
}
pub unsafe fn _init_l_main___boxed__const__1() -> *mut leanh::LeanObject {
    let mut v___x_6631_: u32 = 0;
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6631_ = 1;
    v___x_6632_ = leanh::lean_box_uint32(v___x_6631_);
    return v___x_6632_;
}
pub unsafe fn _init_l_main___boxed__const__2() -> *mut leanh::LeanObject {
    let mut v___x_6633_: u32 = 0;
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6633_ = 0;
    v___x_6634_ = leanh::lean_box_uint32(v___x_6633_);
    return v___x_6634_;
}
pub unsafe fn _lean_main(
    mut v_args_6635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6642_: u8 = 0;
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6647_: u8 = 0;
    let mut v_unused_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6652_: u8 = 0;
    let mut v___x_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6656_: u8 = 0;
    let mut v___x_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6668_: u8 = 0;
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: u8 = 0;
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6688_: u8 = 0;
    let mut v___x_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: u8 = 0;
    let mut v___x_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: u8 = 0;
    let mut v___y_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6728_: u8 = 0;
    let mut v_unreported_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6734_: u8 = 0;
    let mut v___x_6735_: u8 = 0;
    let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: u8 = 0;
    let mut v___x_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: u8 = 0;
    let mut v___x_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6760_: u8 = 0;
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6764_: u8 = 0;
    let mut v_a_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6768_: u8 = 0;
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6772_: u8 = 0;
    let mut v_reuseFailAlloc_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6781_: u8 = 0;
    let mut v___x_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6786_: u8 = 0;
    let mut v_unused_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6791_: u8 = 0;
    let mut v___x_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6795_: u8 = 0;
    let mut v_a_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6799_: u8 = 0;
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6803_: u8 = 0;
    let mut v_a_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6807_: u8 = 0;
    let mut v___x_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6811_: u8 = 0;
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6816_: u8 = 0;
    let mut v_unused_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6821_: u8 = 0;
    let mut v___x_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6825_: u8 = 0;
    let mut v_isSharedCheck_6826_: u8 = 0;
    let mut v_unused_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6838_: u8 = 0;
    let mut v___y_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6868_: usize = 0;
    let mut v___x_6869_: usize = 0;
    let mut v___x_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: u8 = 0;
    let mut v___x_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6881_: u8 = 0;
    let mut v___y_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6894_: u8 = 0;
    let mut v___y_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6914_: u8 = 0;
    let mut v_inheritedTraceOptions_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6918_: u8 = 0;
    let mut v_env_6919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: u8 = 0;
    let mut v___x_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: u8 = 0;
    let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: usize = 0;
    let mut v___x_6937_: usize = 0;
    let mut v___x_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: usize = 0;
    let mut v___x_6941_: usize = 0;
    let mut v___x_6942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6945_: u8 = 0;
    let mut v_unused_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6952_: u8 = 0;
    let mut v___y_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6965_: u8 = 0;
    let mut v___y_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6972_: u8 = 0;
    let mut v___x_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6984_: u8 = 0;
    let mut v___x_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6990_: u8 = 0;
    let mut v_unused_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7001_: u8 = 0;
    let mut v___y_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleData_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: u8 = 0;
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_base_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_private_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_header_7016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_serverBaseExts_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncConstsMap_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncCtx_x3f_7020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importRealizationCtx_x3f_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localRealizationCtxMap_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allRealizations_7023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_7024_: u8 = 0;
    let mut v___x_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7027_: u8 = 0;
    let mut v_public_7028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7031_: u8 = 0;
    let mut v_constants_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotInit_7033_: u8 = 0;
    let mut v_diagnostics_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_const2ModIdx_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irBaseExts_7037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7040_: u8 = 0;
    let mut v_trustLevel_7041_: u32 = 0;
    let mut v_mainModule_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_7043_: u8 = 0;
    let mut v_regions_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleName2Idx_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importAllModules_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleData_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7051_: u8 = 0;
    let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: u8 = 0;
    let mut v___x_7087_: u8 = 0;
    let mut v_reuseFailAlloc_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7092_: u8 = 0;
    let mut v_unused_7093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7094_: u8 = 0;
    let mut v_unused_7095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7096_: u8 = 0;
    let mut v_unused_7097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7098_: u8 = 0;
    let mut v_unused_7099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7105_: u8 = 0;
    let mut v___y_7106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: u8 = 0;
    let mut v___x_7116_: u8 = 0;
    let mut v___x_7117_: usize = 0;
    let mut v___x_7118_: usize = 0;
    let mut v___x_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: usize = 0;
    let mut v___x_7121_: usize = 0;
    let mut v___x_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7128_: u8 = 0;
    let mut v___y_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: u8 = 0;
    let mut v___x_7132_: u8 = 0;
    let mut v___x_7133_: usize = 0;
    let mut v___x_7134_: usize = 0;
    let mut v___x_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: usize = 0;
    let mut v___x_7137_: usize = 0;
    let mut v___x_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7144_: u8 = 0;
    let mut v___y_7145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: u8 = 0;
    let mut v___x_7148_: u8 = 0;
    let mut v___x_7149_: usize = 0;
    let mut v___x_7150_: usize = 0;
    let mut v___x_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: usize = 0;
    let mut v___x_7153_: usize = 0;
    let mut v___x_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: u8 = 0;
    let mut v___y_7159_: u8 = 0;
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7187_: u8 = 0;
    let mut v___x_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: u8 = 0;
    let mut v___x_7192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: u8 = 0;
    let mut v___x_7196_: u8 = 0;
    let mut v___x_7197_: usize = 0;
    let mut v___x_7198_: usize = 0;
    let mut v___x_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: usize = 0;
    let mut v___x_7201_: usize = 0;
    let mut v___x_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7212_: u8 = 0;
    let mut v_a_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7216_: u8 = 0;
    let mut v___x_7218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7220_: u8 = 0;
    let mut v_a_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7224_: u8 = 0;
    let mut v___x_7226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7228_: u8 = 0;
    let mut v_a_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7232_: u8 = 0;
    let mut v___x_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7236_: u8 = 0;
    let mut v_a_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7240_: u8 = 0;
    let mut v___x_7242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7244_: u8 = 0;
    let mut v_a_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7248_: u8 = 0;
    let mut v___x_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7252_: u8 = 0;
    let mut v___x_7253_: u8 = 0;
    let mut v_isSharedCheck_7254_: u8 = 0;
    let mut v_a_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7258_: u8 = 0;
    let mut v___x_7260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7262_: u8 = 0;
    let mut v_a_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7266_: u8 = 0;
    let mut v___x_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7270_: u8 = 0;
    let mut v_a_7271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7274_: u8 = 0;
    let mut v___x_7276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7278_: u8 = 0;
    let mut v_reuseFailAlloc_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7283_: u8 = 0;
    let mut v___x_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7287_: u8 = 0;
    let mut v_isSharedCheck_7288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_args_6635_) == 1 {
                    v_tail_6660_ = leanh::lean_ctor_get(v_args_6635_, 1);
                    leanh::lean_inc(v_tail_6660_);
                    if leanh::lean_obj_tag(v_tail_6660_) == 1 {
                        v_tail_6661_ = leanh::lean_ctor_get(v_tail_6660_, 1);
                        leanh::lean_inc(v_tail_6661_);
                        if leanh::lean_obj_tag(v_tail_6661_) == 1 {
                            v_head_6662_ = leanh::lean_ctor_get(v_args_6635_, 0);
                            leanh::lean_inc(v_head_6662_);
                            leanh::lean_dec_ref_known(v_args_6635_, 2);
                            v_head_6663_ = leanh::lean_ctor_get(v_tail_6660_, 0);
                            leanh::lean_inc(v_head_6663_);
                            leanh::lean_dec_ref_known(v_tail_6660_, 2);
                            v_head_6664_ = leanh::lean_ctor_get(v_tail_6661_, 0);
                            v_tail_6665_ = leanh::lean_ctor_get(v_tail_6661_, 1);
                            v_isSharedCheck_7288_ =
                                (!leanh::lean_is_exclusive(v_tail_6661_)) as u8;
                            if v_isSharedCheck_7288_ == 0 {
                                v___x_6667_ = v_tail_6661_;
                                v_isShared_6668_ = v_isSharedCheck_7288_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_tail_6665_);
                                leanh::lean_inc(v_head_6664_);
                                leanh::lean_dec(v_tail_6661_);
                                v___x_6667_ = leanh::lean_box(0);
                                v_isShared_6668_ = v_isSharedCheck_7288_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_tail_6660_, 2);
                            leanh::lean_dec(v_tail_6661_);
                            leanh::lean_dec_ref_known(v_args_6635_, 2);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tail_6660_);
                        leanh::lean_dec_ref_known(v_args_6635_, 2);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_args_6635_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6638_ = l_main___closed__0;
                v___x_6639_ =
                    l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_6638_);
                if leanh::lean_obj_tag(v___x_6639_) == 0 {
                    v_isSharedCheck_6647_ = (!leanh::lean_is_exclusive(v___x_6639_)) as u8;
                    if v_isSharedCheck_6647_ == 0 {
                        v_unused_6648_ = leanh::lean_ctor_get(v___x_6639_, 0);
                        leanh::lean_dec(v_unused_6648_);
                        v___x_6641_ = v___x_6639_;
                        v_isShared_6642_ = v_isSharedCheck_6647_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6639_);
                        v___x_6641_ = leanh::lean_box(0);
                        v_isShared_6642_ = v_isSharedCheck_6647_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6649_ = leanh::lean_ctor_get(v___x_6639_, 0);
                    v_isSharedCheck_6656_ = (!leanh::lean_is_exclusive(v___x_6639_)) as u8;
                    if v_isSharedCheck_6656_ == 0 {
                        v___x_6651_ = v___x_6639_;
                        v_isShared_6652_ = v_isSharedCheck_6656_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6649_);
                        leanh::lean_dec(v___x_6639_);
                        v___x_6651_ = leanh::lean_box(0);
                        v_isShared_6652_ = v_isSharedCheck_6656_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6643_ = l_main___boxed__const__1;
                if v_isShared_6642_ == 0 {
                    leanh::lean_ctor_set(v___x_6641_, 0, v___x_6643_);
                    v___x_6645_ = v___x_6641_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6646_, 0, v___x_6643_);
                    v___x_6645_ = v_reuseFailAlloc_6646_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6645_;
            }
            4 => {
                if v_isShared_6652_ == 0 {
                    v___x_6654_ = v___x_6651_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6655_, 0, v_a_6649_);
                    v___x_6654_ = v_reuseFailAlloc_6655_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6654_;
            }
            6 => {
                v___x_6658_ = l_main___boxed__const__2;
                v___x_6659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6659_, 0, v___x_6658_);
                return v___x_6659_;
            }
            7 => {
                v___x_6669_ = l_Lean_ModuleSetup_load(v_head_6662_);
                leanh::lean_dec(v_head_6662_);
                if leanh::lean_obj_tag(v___x_6669_) == 0 {
                    v_a_6670_ = leanh::lean_ctor_get(v___x_6669_, 0);
                    leanh::lean_inc(v_a_6670_);
                    leanh::lean_dec_ref_known(v___x_6669_, 1);
                    v_name_6671_ = leanh::lean_ctor_get(v_a_6670_, 0);
                    leanh::lean_inc(v_name_6671_);
                    v_options_6672_ = leanh::lean_ctor_get(v_a_6670_, 6);
                    leanh::lean_inc(v_options_6672_);
                    leanh::lean_dec(v_a_6670_);
                    v___x_6673_ = 0;
                    v___x_6674_ = l_Lean_LeanOptions_toOptions(v_options_6672_);
                    v___x_6675_ = leanh::lean_box((v___x_6673_) as usize);
                    if v_isShared_6668_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6667_, 0);
                        leanh::lean_ctor_set(v___x_6667_, 1, v___x_6674_);
                        leanh::lean_ctor_set(v___x_6667_, 0, v___x_6675_);
                        v___x_6677_ = v___x_6667_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7279_, 0, v___x_6675_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7279_, 1, v___x_6674_);
                        v___x_6677_ = v_reuseFailAlloc_7279_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6667_);
                    leanh::lean_dec(v_tail_6665_);
                    leanh::lean_dec(v_head_6664_);
                    leanh::lean_dec(v_head_6663_);
                    v_a_7280_ = leanh::lean_ctor_get(v___x_6669_, 0);
                    v_isSharedCheck_7287_ = (!leanh::lean_is_exclusive(v___x_6669_)) as u8;
                    if v_isSharedCheck_7287_ == 0 {
                        v___x_7282_ = v___x_6669_;
                        v_isShared_7283_ = v_isSharedCheck_7287_;
                        state = 68;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7280_);
                        leanh::lean_dec(v___x_6669_);
                        v___x_7282_ = leanh::lean_box(0);
                        v_isShared_7283_ = v_isSharedCheck_7287_;
                        state = 68;
                        continue;
                    }
                }
            }
            8 => {
                v___x_6678_ =
                    l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_6665_, v___x_6677_);
                leanh::lean_dec(v_tail_6665_);
                if leanh::lean_obj_tag(v___x_6678_) == 0 {
                    v_a_6679_ = leanh::lean_ctor_get(v___x_6678_, 0);
                    leanh::lean_inc(v_a_6679_);
                    leanh::lean_dec_ref_known(v___x_6678_, 1);
                    v___x_6680_ = l_Lean_getBuildDir();
                    if leanh::lean_obj_tag(v___x_6680_) == 0 {
                        v_a_6681_ = leanh::lean_ctor_get(v___x_6680_, 0);
                        leanh::lean_inc(v_a_6681_);
                        leanh::lean_dec_ref_known(v___x_6680_, 1);
                        v___x_6682_ = leanh::lean_box(0);
                        v___x_6683_ = l_Lean_initSearchPath(v_a_6681_, v___x_6682_);
                        if leanh::lean_obj_tag(v___x_6683_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6683_, 1);
                            v_fst_6684_ = leanh::lean_ctor_get(v_a_6679_, 0);
                            v_snd_6685_ = leanh::lean_ctor_get(v_a_6679_, 1);
                            v_isSharedCheck_7254_ =
                                (!leanh::lean_is_exclusive(v_a_6679_)) as u8;
                            if v_isSharedCheck_7254_ == 0 {
                                v___x_6687_ = v_a_6679_;
                                v_isShared_6688_ = v_isSharedCheck_7254_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_6685_);
                                leanh::lean_inc(v_fst_6684_);
                                leanh::lean_dec(v_a_6679_);
                                v___x_6687_ = leanh::lean_box(0);
                                v_isShared_6688_ = v_isSharedCheck_7254_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6679_);
                            leanh::lean_dec(v_name_6671_);
                            leanh::lean_dec(v_head_6664_);
                            leanh::lean_dec(v_head_6663_);
                            v_a_7255_ = leanh::lean_ctor_get(v___x_6683_, 0);
                            v_isSharedCheck_7262_ =
                                (!leanh::lean_is_exclusive(v___x_6683_)) as u8;
                            if v_isSharedCheck_7262_ == 0 {
                                v___x_7257_ = v___x_6683_;
                                v_isShared_7258_ = v_isSharedCheck_7262_;
                                state = 62;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7255_);
                                leanh::lean_dec(v___x_6683_);
                                v___x_7257_ = leanh::lean_box(0);
                                v_isShared_7258_ = v_isSharedCheck_7262_;
                                state = 62;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_6679_);
                        leanh::lean_dec(v_name_6671_);
                        leanh::lean_dec(v_head_6664_);
                        leanh::lean_dec(v_head_6663_);
                        v_a_7263_ = leanh::lean_ctor_get(v___x_6680_, 0);
                        v_isSharedCheck_7270_ =
                            (!leanh::lean_is_exclusive(v___x_6680_)) as u8;
                        if v_isSharedCheck_7270_ == 0 {
                            v___x_7265_ = v___x_6680_;
                            v_isShared_7266_ = v_isSharedCheck_7270_;
                            state = 64;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7263_);
                            leanh::lean_dec(v___x_6680_);
                            v___x_7265_ = leanh::lean_box(0);
                            v_isShared_7266_ = v_isSharedCheck_7270_;
                            state = 64;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_name_6671_);
                    leanh::lean_dec(v_head_6664_);
                    leanh::lean_dec(v_head_6663_);
                    v_a_7271_ = leanh::lean_ctor_get(v___x_6678_, 0);
                    v_isSharedCheck_7278_ = (!leanh::lean_is_exclusive(v___x_6678_)) as u8;
                    if v_isSharedCheck_7278_ == 0 {
                        v___x_7273_ = v___x_6678_;
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 66;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7271_);
                        leanh::lean_dec(v___x_6678_);
                        v___x_7273_ = leanh::lean_box(0);
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 66;
                        continue;
                    }
                }
            }
            9 => {
                v___x_6689_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__3),
                    core::ptr::addr_of_mut!(l_main___closed__3_once),
                    _init_l_main___closed__3,
                );
                v___x_6690_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__4),
                    core::ptr::addr_of_mut!(l_main___closed__4_once),
                    _init_l_main___closed__4,
                );
                v___x_6691_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__5),
                    core::ptr::addr_of_mut!(l_main___closed__5_once),
                    _init_l_main___closed__5,
                );
                v___x_6692_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__6),
                    core::ptr::addr_of_mut!(l_main___closed__6_once),
                    _init_l_main___closed__6,
                );
                v___x_6693_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__8),
                    core::ptr::addr_of_mut!(l_main___closed__8_once),
                    _init_l_main___closed__8,
                );
                v___x_6694_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__9),
                    core::ptr::addr_of_mut!(l_main___closed__9_once),
                    _init_l_main___closed__9,
                );
                v___x_6695_ = leanh::lean_box(1);
                v___x_6696_ = l_main___closed__10;
                v___x_6697_ = l_Lean_Compiler_compiler_inLeanIR;
                v___x_6698_ = 1;
                v___x_6699_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(
                    v_snd_6685_,
                    v___x_6697_,
                    v___x_6698_,
                );
                v___x_6700_ = l_Lean_maxHeartbeats;
                v___x_6701_ = leanh::lean_unsigned_to_nat(0);
                v___x_6702_ =
                    l_Lean_Option_set___at___00main_spec__3(v___x_6699_, v___x_6700_, v___x_6701_);
                v___x_6992_ = l_main___closed__20;
                leanh::lean_inc(v_name_6671_);
                v___x_6993_ = leanh::lean_alloc_ctor(0, 1, (3) as u32);
                leanh::lean_ctor_set(v___x_6993_, 0, v_name_6671_);
                leanh::lean_ctor_set_uint8(
                    v___x_6993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6698_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v___x_6698_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                    v___x_6698_,
                );
                v___x_6994_ = leanh::lean_unsigned_to_nat(1);
                v___x_7155_ = lean_mk_empty_array_with_capacity(v___x_6994_);
                v___x_7156_ = lean_array_push(v___x_7155_, v___x_6993_);
                v___x_7157_ = 2;
                v___x_7253_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_main___closed__36),
                    core::ptr::addr_of_mut!(l_main___closed__36_once),
                    _init_l_main___closed__36,
                );
                if v___x_7253_ == 0 {
                    v___y_7159_ = v___x_6698_;
                    state = 49;
                    continue;
                } else {
                    v___y_7159_ = v___x_6673_;
                    state = 49;
                    continue;
                }
            }
            10 => {
                v___x_6723_ = lean_st_ref_get(v___y_6719_);
                leanh::lean_dec(v___y_6719_);
                v_messages_6724_ = leanh::lean_ctor_get(v___x_6723_, 6);
                v_env_6725_ = leanh::lean_ctor_get(v___x_6723_, 0);
                v_isSharedCheck_6826_ = (!leanh::lean_is_exclusive(v___x_6723_)) as u8;
                if v_isSharedCheck_6826_ == 0 {
                    v_unused_6827_ = leanh::lean_ctor_get(v___x_6723_, 8);
                    leanh::lean_dec(v_unused_6827_);
                    v_unused_6828_ = leanh::lean_ctor_get(v___x_6723_, 7);
                    leanh::lean_dec(v_unused_6828_);
                    v_unused_6829_ = leanh::lean_ctor_get(v___x_6723_, 5);
                    leanh::lean_dec(v_unused_6829_);
                    v_unused_6830_ = leanh::lean_ctor_get(v___x_6723_, 4);
                    leanh::lean_dec(v_unused_6830_);
                    v_unused_6831_ = leanh::lean_ctor_get(v___x_6723_, 3);
                    leanh::lean_dec(v_unused_6831_);
                    v_unused_6832_ = leanh::lean_ctor_get(v___x_6723_, 2);
                    leanh::lean_dec(v_unused_6832_);
                    v_unused_6833_ = leanh::lean_ctor_get(v___x_6723_, 1);
                    leanh::lean_dec(v_unused_6833_);
                    v___x_6727_ = v___x_6723_;
                    v_isShared_6728_ = v_isSharedCheck_6826_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_messages_6724_);
                    leanh::lean_inc(v_env_6725_);
                    leanh::lean_dec(v___x_6723_);
                    v___x_6727_ = leanh::lean_box(0);
                    v_isShared_6728_ = v_isSharedCheck_6826_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_unreported_6729_ = leanh::lean_ctor_get(v_messages_6724_, 1);
                v___x_6730_ = leanh::lean_box(0);
                v___x_6731_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(
                    v_unreported_6729_,
                    v___x_6730_,
                );
                if leanh::lean_obj_tag(v___x_6731_) == 0 {
                    v_isSharedCheck_6816_ = (!leanh::lean_is_exclusive(v___x_6731_)) as u8;
                    if v_isSharedCheck_6816_ == 0 {
                        v_unused_6817_ = leanh::lean_ctor_get(v___x_6731_, 0);
                        leanh::lean_dec(v_unused_6817_);
                        v___x_6733_ = v___x_6731_;
                        v_isShared_6734_ = v_isSharedCheck_6816_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6731_);
                        v___x_6733_ = leanh::lean_box(0);
                        v_isShared_6734_ = v_isSharedCheck_6816_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6727_);
                    leanh::lean_dec_ref(v_env_6725_);
                    leanh::lean_dec_ref(v_messages_6724_);
                    leanh::lean_dec_ref(v___y_6718_);
                    leanh::lean_dec(v___y_6715_);
                    leanh::lean_dec(v___y_6710_);
                    leanh::lean_dec(v___y_6704_);
                    leanh::lean_dec_ref(v___x_6702_);
                    leanh::lean_dec(v_fst_6684_);
                    leanh::lean_dec(v_name_6671_);
                    leanh::lean_dec(v_head_6664_);
                    leanh::lean_dec(v_head_6663_);
                    v_a_6818_ = leanh::lean_ctor_get(v___x_6731_, 0);
                    v_isSharedCheck_6825_ = (!leanh::lean_is_exclusive(v___x_6731_)) as u8;
                    if v_isSharedCheck_6825_ == 0 {
                        v___x_6820_ = v___x_6731_;
                        v_isShared_6821_ = v_isSharedCheck_6825_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6818_);
                        leanh::lean_dec(v___x_6731_);
                        v___x_6820_ = leanh::lean_box(0);
                        v_isShared_6821_ = v_isSharedCheck_6825_;
                        state = 27;
                        continue;
                    }
                }
            }
            12 => {
                v___x_6735_ = l_Lean_MessageLog_hasErrors(v_messages_6724_);
                leanh::lean_dec_ref(v_messages_6724_);
                if v___x_6735_ == 0 {
                    leanh::lean_del_object(v___x_6733_);
                    leanh::lean_inc_ref(v_env_6725_);
                    v___x_6736_ = l___private_LeanIR_0__mkIRData(v_env_6725_);
                    if leanh::lean_obj_tag(v___x_6736_) == 0 {
                        v_a_6737_ = leanh::lean_ctor_get(v___x_6736_, 0);
                        leanh::lean_inc(v_a_6737_);
                        leanh::lean_dec_ref_known(v___x_6736_, 1);
                        v___x_6738_ = l_Lean_Environment_mainModule(v_env_6725_);
                        v___x_6739_ = l_main___closed__12;
                        v___x_6740_ = l_Lean_Name_append(v___x_6738_, v___x_6739_);
                        v___x_6741_ = l_Lean_saveModuleData(v_head_6663_, v___x_6740_, v_a_6737_);
                        leanh::lean_dec(v_a_6737_);
                        leanh::lean_dec(v___x_6740_);
                        if leanh::lean_obj_tag(v___x_6741_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6741_, 1);
                            v___x_6742_ = 1;
                            v___x_6743_ = lean_io_prim_handle_mk(v_head_6664_, v___x_6742_);
                            if leanh::lean_obj_tag(v___x_6743_) == 0 {
                                leanh::lean_dec(v_head_6664_);
                                v_a_6744_ = leanh::lean_ctor_get(v___x_6743_, 0);
                                leanh::lean_inc(v_a_6744_);
                                leanh::lean_dec_ref_known(v___x_6743_, 1);
                                v___x_6745_ = l_main___closed__13;
                                v___x_6746_ = l_Lean_Options_empty;
                                v___x_6747_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_main___closed__14),
                                    core::ptr::addr_of_mut!(l_main___closed__14_once),
                                    _init_l_main___closed__14,
                                );
                                leanh::lean_inc_ref(v___y_6714_);
                                leanh::lean_inc_ref(v___y_6716_);
                                leanh::lean_inc_ref(v___y_6720_);
                                leanh::lean_inc_ref(v___y_6722_);
                                leanh::lean_inc_ref(v___y_6721_);
                                leanh::lean_inc_ref(v___y_6717_);
                                leanh::lean_inc(v___y_6713_);
                                leanh::lean_inc_ref(v_env_6725_);
                                if v_isShared_6728_ == 0 {
                                    leanh::lean_ctor_set(v___x_6727_, 8, v___y_6714_);
                                    leanh::lean_ctor_set(v___x_6727_, 7, v___y_6716_);
                                    leanh::lean_ctor_set(v___x_6727_, 6, v___y_6720_);
                                    leanh::lean_ctor_set(v___x_6727_, 5, v___y_6722_);
                                    leanh::lean_ctor_set(v___x_6727_, 4, v___y_6721_);
                                    leanh::lean_ctor_set(v___x_6727_, 3, v___y_6718_);
                                    leanh::lean_ctor_set(v___x_6727_, 2, v___y_6717_);
                                    leanh::lean_ctor_set(v___x_6727_, 1, v___y_6713_);
                                    v___x_6749_ = v___x_6727_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6773_ =
                                        leanh::lean_alloc_ctor(0, 9, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        0,
                                        v_env_6725_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        1,
                                        v___y_6713_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        2,
                                        v___y_6717_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        3,
                                        v___y_6718_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        4,
                                        v___y_6721_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        5,
                                        v___y_6722_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        6,
                                        v___y_6720_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        7,
                                        v___y_6716_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6773_,
                                        8,
                                        v___y_6714_,
                                    );
                                    v___x_6749_ = v_reuseFailAlloc_6773_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v___x_6743_, 1);
                                leanh::lean_del_object(v___x_6727_);
                                leanh::lean_dec_ref(v_env_6725_);
                                leanh::lean_dec_ref(v___y_6718_);
                                leanh::lean_dec(v___y_6715_);
                                leanh::lean_dec(v___y_6710_);
                                leanh::lean_dec(v___y_6704_);
                                leanh::lean_dec_ref(v___x_6702_);
                                leanh::lean_dec(v_fst_6684_);
                                leanh::lean_dec(v_name_6671_);
                                leanh::lean_dec(v_head_6663_);
                                v___x_6774_ = l_main___closed__15;
                                v___x_6775_ = lean_string_append(v___x_6774_, v_head_6664_);
                                leanh::lean_dec(v_head_6664_);
                                v___x_6776_ = l___private_LeanIR_0__setConfigOption___closed__1;
                                v___x_6777_ = lean_string_append(v___x_6775_, v___x_6776_);
                                v___x_6778_ = l_IO_eprintln___at___00main_spec__6(v___x_6777_);
                                if leanh::lean_obj_tag(v___x_6778_) == 0 {
                                    v_isSharedCheck_6786_ =
                                        (!leanh::lean_is_exclusive(v___x_6778_)) as u8;
                                    if v_isSharedCheck_6786_ == 0 {
                                        v_unused_6787_ =
                                            leanh::lean_ctor_get(v___x_6778_, 0);
                                        leanh::lean_dec(v_unused_6787_);
                                        v___x_6780_ = v___x_6778_;
                                        v_isShared_6781_ = v_isSharedCheck_6786_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_6778_);
                                        v___x_6780_ = leanh::lean_box(0);
                                        v_isShared_6781_ = v_isSharedCheck_6786_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v_a_6788_ = leanh::lean_ctor_get(v___x_6778_, 0);
                                    v_isSharedCheck_6795_ =
                                        (!leanh::lean_is_exclusive(v___x_6778_)) as u8;
                                    if v_isSharedCheck_6795_ == 0 {
                                        v___x_6790_ = v___x_6778_;
                                        v_isShared_6791_ = v_isSharedCheck_6795_;
                                        state = 20;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6788_);
                                        leanh::lean_dec(v___x_6778_);
                                        v___x_6790_ = leanh::lean_box(0);
                                        v_isShared_6791_ = v_isSharedCheck_6795_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_6727_);
                            leanh::lean_dec_ref(v_env_6725_);
                            leanh::lean_dec_ref(v___y_6718_);
                            leanh::lean_dec(v___y_6715_);
                            leanh::lean_dec(v___y_6710_);
                            leanh::lean_dec(v___y_6704_);
                            leanh::lean_dec_ref(v___x_6702_);
                            leanh::lean_dec(v_fst_6684_);
                            leanh::lean_dec(v_name_6671_);
                            leanh::lean_dec(v_head_6664_);
                            leanh::lean_dec(v_head_6663_);
                            v_a_6796_ = leanh::lean_ctor_get(v___x_6741_, 0);
                            v_isSharedCheck_6803_ =
                                (!leanh::lean_is_exclusive(v___x_6741_)) as u8;
                            if v_isSharedCheck_6803_ == 0 {
                                v___x_6798_ = v___x_6741_;
                                v_isShared_6799_ = v_isSharedCheck_6803_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6796_);
                                leanh::lean_dec(v___x_6741_);
                                v___x_6798_ = leanh::lean_box(0);
                                v_isShared_6799_ = v_isSharedCheck_6803_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_6727_);
                        leanh::lean_dec_ref(v_env_6725_);
                        leanh::lean_dec_ref(v___y_6718_);
                        leanh::lean_dec(v___y_6715_);
                        leanh::lean_dec(v___y_6710_);
                        leanh::lean_dec(v___y_6704_);
                        leanh::lean_dec_ref(v___x_6702_);
                        leanh::lean_dec(v_fst_6684_);
                        leanh::lean_dec(v_name_6671_);
                        leanh::lean_dec(v_head_6664_);
                        leanh::lean_dec(v_head_6663_);
                        v_a_6804_ = leanh::lean_ctor_get(v___x_6736_, 0);
                        v_isSharedCheck_6811_ =
                            (!leanh::lean_is_exclusive(v___x_6736_)) as u8;
                        if v_isSharedCheck_6811_ == 0 {
                            v___x_6806_ = v___x_6736_;
                            v_isShared_6807_ = v_isSharedCheck_6811_;
                            state = 24;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6804_);
                            leanh::lean_dec(v___x_6736_);
                            v___x_6806_ = leanh::lean_box(0);
                            v_isShared_6807_ = v_isSharedCheck_6811_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_6727_);
                    leanh::lean_dec_ref(v_env_6725_);
                    leanh::lean_dec_ref(v___y_6718_);
                    leanh::lean_dec(v___y_6715_);
                    leanh::lean_dec(v___y_6710_);
                    leanh::lean_dec(v___y_6704_);
                    leanh::lean_dec_ref(v___x_6702_);
                    leanh::lean_dec(v_fst_6684_);
                    leanh::lean_dec(v_name_6671_);
                    leanh::lean_dec(v_head_6664_);
                    leanh::lean_dec(v_head_6663_);
                    v___x_6812_ = l_main___boxed__const__1;
                    if v_isShared_6734_ == 0 {
                        leanh::lean_ctor_set(v___x_6733_, 0, v___x_6812_);
                        v___x_6814_ = v___x_6733_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_6815_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6815_, 0, v___x_6812_);
                        v___x_6814_ = v_reuseFailAlloc_6815_;
                        state = 26;
                        continue;
                    }
                }
            }
            13 => {
                v___x_6750_ = leanh::lean_box((v___x_6673_) as usize);
                v___x_6751_ = leanh::lean_box((v___y_6707_) as usize);
                leanh::lean_inc(v___y_6708_);
                leanh::lean_inc(v___y_6709_);
                leanh::lean_inc(v___y_6705_);
                leanh::lean_inc_ref(v___y_6706_);
                leanh::lean_inc_ref(v___y_6712_);
                leanh::lean_inc(v___y_6711_);
                v___f_6752_ = leanh::lean_alloc_closure(
                    l_main___lam__1___boxed as *mut core::ffi::c_void,
                    18,
                    17,
                );
                leanh::lean_closure_set(v___f_6752_, 0, v___x_6749_);
                leanh::lean_closure_set(v___f_6752_, 1, v___y_6711_);
                leanh::lean_closure_set(v___f_6752_, 2, v___x_6746_);
                leanh::lean_closure_set(v___f_6752_, 3, v_name_6671_);
                leanh::lean_closure_set(v___f_6752_, 4, v_a_6744_);
                leanh::lean_closure_set(v___f_6752_, 5, v___y_6712_);
                leanh::lean_closure_set(v___f_6752_, 6, v_head_6663_);
                leanh::lean_closure_set(v___f_6752_, 7, v___y_6706_);
                leanh::lean_closure_set(v___f_6752_, 8, v___x_6701_);
                leanh::lean_closure_set(v___f_6752_, 9, v___y_6705_);
                leanh::lean_closure_set(v___f_6752_, 10, v___y_6704_);
                leanh::lean_closure_set(v___f_6752_, 11, v___y_6710_);
                leanh::lean_closure_set(v___f_6752_, 12, v___x_6747_);
                leanh::lean_closure_set(v___f_6752_, 13, v___y_6709_);
                leanh::lean_closure_set(v___f_6752_, 14, v___y_6708_);
                leanh::lean_closure_set(v___f_6752_, 15, v___x_6750_);
                leanh::lean_closure_set(v___f_6752_, 16, v___x_6751_);
                v___x_6753_ = l_Lean_profileitIOUnsafe___redArg(
                    v___x_6745_,
                    v___x_6702_,
                    v___f_6752_,
                    v___y_6715_,
                );
                leanh::lean_dec_ref(v___x_6702_);
                if leanh::lean_obj_tag(v___x_6753_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6753_, 1);
                    v___x_6754_ = lean_display_cumulative_profiling_times();
                    v___x_6755_ = (leanh::lean_unbox(v_fst_6684_) as u8);
                    leanh::lean_dec(v_fst_6684_);
                    if v___x_6755_ == 0 {
                        leanh::lean_dec_ref(v_env_6725_);
                        state = 6;
                        continue;
                    } else {
                        v___x_6756_ = l_Lean_Environment_displayStats(v_env_6725_);
                        if leanh::lean_obj_tag(v___x_6756_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6756_, 1);
                            state = 6;
                            continue;
                        } else {
                            v_a_6757_ = leanh::lean_ctor_get(v___x_6756_, 0);
                            v_isSharedCheck_6764_ =
                                (!leanh::lean_is_exclusive(v___x_6756_)) as u8;
                            if v_isSharedCheck_6764_ == 0 {
                                v___x_6759_ = v___x_6756_;
                                v_isShared_6760_ = v_isSharedCheck_6764_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6757_);
                                leanh::lean_dec(v___x_6756_);
                                v___x_6759_ = leanh::lean_box(0);
                                v_isShared_6760_ = v_isSharedCheck_6764_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_6725_);
                    leanh::lean_dec(v_fst_6684_);
                    v_a_6765_ = leanh::lean_ctor_get(v___x_6753_, 0);
                    v_isSharedCheck_6772_ = (!leanh::lean_is_exclusive(v___x_6753_)) as u8;
                    if v_isSharedCheck_6772_ == 0 {
                        v___x_6767_ = v___x_6753_;
                        v_isShared_6768_ = v_isSharedCheck_6772_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6765_);
                        leanh::lean_dec(v___x_6753_);
                        v___x_6767_ = leanh::lean_box(0);
                        v_isShared_6768_ = v_isSharedCheck_6772_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_6760_ == 0 {
                    v___x_6762_ = v___x_6759_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6763_, 0, v_a_6757_);
                    v___x_6762_ = v_reuseFailAlloc_6763_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6762_;
            }
            16 => {
                if v_isShared_6768_ == 0 {
                    v___x_6770_ = v___x_6767_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6771_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6771_, 0, v_a_6765_);
                    v___x_6770_ = v_reuseFailAlloc_6771_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6770_;
            }
            18 => {
                v___x_6782_ = l_main___boxed__const__1;
                if v_isShared_6781_ == 0 {
                    leanh::lean_ctor_set(v___x_6780_, 0, v___x_6782_);
                    v___x_6784_ = v___x_6780_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6785_, 0, v___x_6782_);
                    v___x_6784_ = v_reuseFailAlloc_6785_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6784_;
            }
            20 => {
                if v_isShared_6791_ == 0 {
                    v___x_6793_ = v___x_6790_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6794_, 0, v_a_6788_);
                    v___x_6793_ = v_reuseFailAlloc_6794_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6793_;
            }
            22 => {
                if v_isShared_6799_ == 0 {
                    v___x_6801_ = v___x_6798_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 0, v_a_6796_);
                    v___x_6801_ = v_reuseFailAlloc_6802_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6801_;
            }
            24 => {
                if v_isShared_6807_ == 0 {
                    v___x_6809_ = v___x_6806_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6810_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6810_, 0, v_a_6804_);
                    v___x_6809_ = v_reuseFailAlloc_6810_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6809_;
            }
            26 => {
                return v___x_6814_;
            }
            27 => {
                if v_isShared_6821_ == 0 {
                    v___x_6823_ = v___x_6820_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6824_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6824_, 0, v_a_6818_);
                    v___x_6823_ = v_reuseFailAlloc_6824_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6823_;
            }
            29 => {
                leanh::lean_inc_ref(v___y_6863_);
                v___x_6865_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_6865_, 0, v___y_6864_);
                leanh::lean_ctor_set(v___x_6865_, 1, v_nextMacroScope_6855_);
                leanh::lean_ctor_set(v___x_6865_, 2, v_ngen_6856_);
                leanh::lean_ctor_set(v___x_6865_, 3, v_auxDeclNGen_6857_);
                leanh::lean_ctor_set(v___x_6865_, 4, v_traceState_6858_);
                leanh::lean_ctor_set(v___x_6865_, 5, v___y_6863_);
                leanh::lean_ctor_set(v___x_6865_, 6, v_messages_6859_);
                leanh::lean_ctor_set(v___x_6865_, 7, v_infoState_6860_);
                leanh::lean_ctor_set(v___x_6865_, 8, v_snapshotTasks_6861_);
                v___x_6866_ = lean_st_ref_set(v___y_6849_, v___x_6865_);
                v___x_6867_ = leanh::lean_box(0);
                v_sz_6868_ = lean_array_size(v___y_6848_);
                v___x_6869_ = 0usize;
                v___x_6870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_6848_, v_sz_6868_, v___x_6869_, v___x_6867_, v___y_6844_, v___y_6849_);
                leanh::lean_dec_ref(v___y_6848_);
                if leanh::lean_obj_tag(v___x_6870_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6870_, 1);
                    leanh::lean_dec(v___y_6849_);
                    leanh::lean_dec_ref(v___y_6844_);
                    v___y_6704_ = v___y_6835_;
                    v___y_6705_ = v___y_6836_;
                    v___y_6706_ = v___y_6837_;
                    v___y_6707_ = v___y_6838_;
                    v___y_6708_ = v___y_6840_;
                    v___y_6709_ = v___y_6839_;
                    v___y_6710_ = v___y_6841_;
                    v___y_6711_ = v___y_6842_;
                    v___y_6712_ = v___y_6843_;
                    v___y_6713_ = v___y_6850_;
                    v___y_6714_ = v___y_6851_;
                    v___y_6715_ = v___y_6845_;
                    v___y_6716_ = v___y_6846_;
                    v___y_6717_ = v___y_6847_;
                    v___y_6718_ = v___y_6852_;
                    v___y_6719_ = v___y_6853_;
                    v___y_6720_ = v___y_6854_;
                    v___y_6721_ = v___y_6862_;
                    v___y_6722_ = v___y_6863_;
                    state = 10;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_6870_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6870_, 1);
                        leanh::lean_dec(v___y_6849_);
                        leanh::lean_dec_ref(v___y_6844_);
                        v___y_6704_ = v___y_6835_;
                        v___y_6705_ = v___y_6836_;
                        v___y_6706_ = v___y_6837_;
                        v___y_6707_ = v___y_6838_;
                        v___y_6708_ = v___y_6840_;
                        v___y_6709_ = v___y_6839_;
                        v___y_6710_ = v___y_6841_;
                        v___y_6711_ = v___y_6842_;
                        v___y_6712_ = v___y_6843_;
                        v___y_6713_ = v___y_6850_;
                        v___y_6714_ = v___y_6851_;
                        v___y_6715_ = v___y_6845_;
                        v___y_6716_ = v___y_6846_;
                        v___y_6717_ = v___y_6847_;
                        v___y_6718_ = v___y_6852_;
                        v___y_6719_ = v___y_6853_;
                        v___y_6720_ = v___y_6854_;
                        v___y_6721_ = v___y_6862_;
                        v___y_6722_ = v___y_6863_;
                        state = 10;
                        continue;
                    } else {
                        v_a_6871_ = leanh::lean_ctor_get(v___x_6870_, 0);
                        leanh::lean_inc(v_a_6871_);
                        leanh::lean_dec_ref_known(v___x_6870_, 1);
                        v___x_6872_ = l_Lean_Exception_isInterrupt(v_a_6871_);
                        if v___x_6872_ == 0 {
                            v___x_6873_ = l_Lean_Exception_toMessageData(v_a_6871_);
                            v___x_6874_ = l_Lean_logError___at___00main_spec__14(
                                v___x_6873_,
                                v___y_6844_,
                                v___y_6849_,
                            );
                            leanh::lean_dec(v___y_6849_);
                            leanh::lean_dec_ref(v___y_6844_);
                            if leanh::lean_obj_tag(v___x_6874_) == 0 {
                                leanh::lean_dec_ref_known(v___x_6874_, 1);
                                v___y_6704_ = v___y_6835_;
                                v___y_6705_ = v___y_6836_;
                                v___y_6706_ = v___y_6837_;
                                v___y_6707_ = v___y_6838_;
                                v___y_6708_ = v___y_6840_;
                                v___y_6709_ = v___y_6839_;
                                v___y_6710_ = v___y_6841_;
                                v___y_6711_ = v___y_6842_;
                                v___y_6712_ = v___y_6843_;
                                v___y_6713_ = v___y_6850_;
                                v___y_6714_ = v___y_6851_;
                                v___y_6715_ = v___y_6845_;
                                v___y_6716_ = v___y_6846_;
                                v___y_6717_ = v___y_6847_;
                                v___y_6718_ = v___y_6852_;
                                v___y_6719_ = v___y_6853_;
                                v___y_6720_ = v___y_6854_;
                                v___y_6721_ = v___y_6862_;
                                v___y_6722_ = v___y_6863_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v___x_6874_, 1);
                                leanh::lean_dec(v___y_6853_);
                                leanh::lean_dec_ref(v___y_6852_);
                                leanh::lean_dec(v___y_6845_);
                                leanh::lean_dec(v___y_6841_);
                                leanh::lean_dec(v___y_6835_);
                                leanh::lean_dec_ref(v___x_6702_);
                                leanh::lean_dec(v_fst_6684_);
                                leanh::lean_dec(v_name_6671_);
                                leanh::lean_dec(v_head_6664_);
                                leanh::lean_dec(v_head_6663_);
                                v___x_6875_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_main___closed__19),
                                    core::ptr::addr_of_mut!(l_main___closed__19_once),
                                    _init_l_main___closed__19,
                                );
                                v___x_6876_ = l_panic___at___00main_spec__5(v___x_6875_);
                                return v___x_6876_;
                            }
                        } else {
                            leanh::lean_dec(v_a_6871_);
                            leanh::lean_dec(v___y_6849_);
                            leanh::lean_dec_ref(v___y_6844_);
                            v___y_6704_ = v___y_6835_;
                            v___y_6705_ = v___y_6836_;
                            v___y_6706_ = v___y_6837_;
                            v___y_6707_ = v___y_6838_;
                            v___y_6708_ = v___y_6840_;
                            v___y_6709_ = v___y_6839_;
                            v___y_6710_ = v___y_6841_;
                            v___y_6711_ = v___y_6842_;
                            v___y_6712_ = v___y_6843_;
                            v___y_6713_ = v___y_6850_;
                            v___y_6714_ = v___y_6851_;
                            v___y_6715_ = v___y_6845_;
                            v___y_6716_ = v___y_6846_;
                            v___y_6717_ = v___y_6847_;
                            v___y_6718_ = v___y_6852_;
                            v___y_6719_ = v___y_6853_;
                            v___y_6720_ = v___y_6854_;
                            v___y_6721_ = v___y_6862_;
                            v___y_6722_ = v___y_6863_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            30 => {
                v___x_6902_ = lean_st_ref_take(v___y_6901_);
                v_fileName_6903_ = leanh::lean_ctor_get(v___y_6900_, 0);
                v_fileMap_6904_ = leanh::lean_ctor_get(v___y_6900_, 1);
                v_currRecDepth_6905_ = leanh::lean_ctor_get(v___y_6900_, 3);
                v_ref_6906_ = leanh::lean_ctor_get(v___y_6900_, 5);
                v_currNamespace_6907_ = leanh::lean_ctor_get(v___y_6900_, 6);
                v_openDecls_6908_ = leanh::lean_ctor_get(v___y_6900_, 7);
                v_initHeartbeats_6909_ = leanh::lean_ctor_get(v___y_6900_, 8);
                v_maxHeartbeats_6910_ = leanh::lean_ctor_get(v___y_6900_, 9);
                v_quotContext_6911_ = leanh::lean_ctor_get(v___y_6900_, 10);
                v_currMacroScope_6912_ = leanh::lean_ctor_get(v___y_6900_, 11);
                v_cancelTk_x3f_6913_ = leanh::lean_ctor_get(v___y_6900_, 12);
                v_suppressElabErrors_6914_ = leanh::lean_ctor_get_uint8(
                    v___y_6900_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6915_ = leanh::lean_ctor_get(v___y_6900_, 13);
                v_isSharedCheck_6945_ = (!leanh::lean_is_exclusive(v___y_6900_)) as u8;
                if v_isSharedCheck_6945_ == 0 {
                    v_unused_6946_ = leanh::lean_ctor_get(v___y_6900_, 4);
                    leanh::lean_dec(v_unused_6946_);
                    v_unused_6947_ = leanh::lean_ctor_get(v___y_6900_, 2);
                    leanh::lean_dec(v_unused_6947_);
                    v___x_6917_ = v___y_6900_;
                    v_isShared_6918_ = v_isSharedCheck_6945_;
                    state = 31;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_6915_);
                    leanh::lean_inc(v_cancelTk_x3f_6913_);
                    leanh::lean_inc(v_currMacroScope_6912_);
                    leanh::lean_inc(v_quotContext_6911_);
                    leanh::lean_inc(v_maxHeartbeats_6910_);
                    leanh::lean_inc(v_initHeartbeats_6909_);
                    leanh::lean_inc(v_openDecls_6908_);
                    leanh::lean_inc(v_currNamespace_6907_);
                    leanh::lean_inc(v_ref_6906_);
                    leanh::lean_inc(v_currRecDepth_6905_);
                    leanh::lean_inc(v_fileMap_6904_);
                    leanh::lean_inc(v_fileName_6903_);
                    leanh::lean_dec(v___y_6900_);
                    v___x_6917_ = leanh::lean_box(0);
                    v_isShared_6918_ = v_isSharedCheck_6945_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v_env_6919_ = leanh::lean_ctor_get(v___x_6902_, 0);
                leanh::lean_inc_ref(v_env_6919_);
                v_nextMacroScope_6920_ = leanh::lean_ctor_get(v___x_6902_, 1);
                leanh::lean_inc(v_nextMacroScope_6920_);
                v_ngen_6921_ = leanh::lean_ctor_get(v___x_6902_, 2);
                leanh::lean_inc_ref(v_ngen_6921_);
                v_auxDeclNGen_6922_ = leanh::lean_ctor_get(v___x_6902_, 3);
                leanh::lean_inc_ref(v_auxDeclNGen_6922_);
                v_traceState_6923_ = leanh::lean_ctor_get(v___x_6902_, 4);
                leanh::lean_inc_ref(v_traceState_6923_);
                v_messages_6924_ = leanh::lean_ctor_get(v___x_6902_, 6);
                leanh::lean_inc_ref(v_messages_6924_);
                v_infoState_6925_ = leanh::lean_ctor_get(v___x_6902_, 7);
                leanh::lean_inc_ref(v_infoState_6925_);
                v_snapshotTasks_6926_ = leanh::lean_ctor_get(v___x_6902_, 8);
                leanh::lean_inc_ref(v_snapshotTasks_6926_);
                leanh::lean_dec(v___x_6902_);
                v___x_6927_ = l_Lean_maxRecDepth;
                v___x_6928_ = l_Lean_Option_get___at___00main_spec__9(v___x_6702_, v___x_6927_);
                leanh::lean_inc_ref(v___x_6702_);
                if v_isShared_6918_ == 0 {
                    leanh::lean_ctor_set(v___x_6917_, 4, v___x_6928_);
                    leanh::lean_ctor_set(v___x_6917_, 2, v___x_6702_);
                    v___x_6930_ = v___x_6917_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6944_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 0, v_fileName_6903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 1, v_fileMap_6904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 2, v___x_6702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 3, v_currRecDepth_6905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 4, v___x_6928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 5, v_ref_6906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 6, v_currNamespace_6907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 7, v_openDecls_6908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 8, v_initHeartbeats_6909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 9, v_maxHeartbeats_6910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 10, v_quotContext_6911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 11, v_currMacroScope_6912_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 12, v_cancelTk_x3f_6913_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6944_,
                        13,
                        v_inheritedTraceOptions_6915_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6944_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_6914_,
                    );
                    v___x_6930_ = v_reuseFailAlloc_6944_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                leanh::lean_ctor_set_uint8(
                    v___x_6930_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_6894_,
                );
                v___x_6931_ = lean_array_get_size(v___y_6891_);
                v___x_6932_ = lean_nat_dec_lt(v___x_6701_, v___x_6931_);
                if v___x_6932_ == 0 {
                    leanh::lean_inc_ref(v___y_6887_);
                    v___x_6933_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(
                        v___y_6887_,
                        v_env_6919_,
                        v___x_6695_,
                    );
                    v___y_6835_ = v___y_6878_;
                    v___y_6836_ = v___y_6879_;
                    v___y_6837_ = v___y_6880_;
                    v___y_6838_ = v___y_6881_;
                    v___y_6839_ = v___y_6883_;
                    v___y_6840_ = v___y_6882_;
                    v___y_6841_ = v___y_6884_;
                    v___y_6842_ = v___y_6885_;
                    v___y_6843_ = v___y_6886_;
                    v___y_6844_ = v___x_6930_;
                    v___y_6845_ = v___y_6888_;
                    v___y_6846_ = v___y_6889_;
                    v___y_6847_ = v___y_6890_;
                    v___y_6848_ = v___y_6891_;
                    v___y_6849_ = v___y_6901_;
                    v___y_6850_ = v___y_6892_;
                    v___y_6851_ = v___y_6893_;
                    v___y_6852_ = v___y_6895_;
                    v___y_6853_ = v___y_6896_;
                    v___y_6854_ = v___y_6897_;
                    v_nextMacroScope_6855_ = v_nextMacroScope_6920_;
                    v_ngen_6856_ = v_ngen_6921_;
                    v_auxDeclNGen_6857_ = v_auxDeclNGen_6922_;
                    v_traceState_6858_ = v_traceState_6923_;
                    v_messages_6859_ = v_messages_6924_;
                    v_infoState_6860_ = v_infoState_6925_;
                    v_snapshotTasks_6861_ = v_snapshotTasks_6926_;
                    v___y_6862_ = v___y_6898_;
                    v___y_6863_ = v___y_6899_;
                    v___y_6864_ = v___x_6933_;
                    state = 29;
                    continue;
                } else {
                    v___x_6934_ = lean_nat_dec_le(v___x_6931_, v___x_6931_);
                    if v___x_6934_ == 0 {
                        if v___x_6932_ == 0 {
                            leanh::lean_inc_ref(v___y_6887_);
                            v___x_6935_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(
                                v___y_6887_,
                                v_env_6919_,
                                v___x_6695_,
                            );
                            v___y_6835_ = v___y_6878_;
                            v___y_6836_ = v___y_6879_;
                            v___y_6837_ = v___y_6880_;
                            v___y_6838_ = v___y_6881_;
                            v___y_6839_ = v___y_6883_;
                            v___y_6840_ = v___y_6882_;
                            v___y_6841_ = v___y_6884_;
                            v___y_6842_ = v___y_6885_;
                            v___y_6843_ = v___y_6886_;
                            v___y_6844_ = v___x_6930_;
                            v___y_6845_ = v___y_6888_;
                            v___y_6846_ = v___y_6889_;
                            v___y_6847_ = v___y_6890_;
                            v___y_6848_ = v___y_6891_;
                            v___y_6849_ = v___y_6901_;
                            v___y_6850_ = v___y_6892_;
                            v___y_6851_ = v___y_6893_;
                            v___y_6852_ = v___y_6895_;
                            v___y_6853_ = v___y_6896_;
                            v___y_6854_ = v___y_6897_;
                            v_nextMacroScope_6855_ = v_nextMacroScope_6920_;
                            v_ngen_6856_ = v_ngen_6921_;
                            v_auxDeclNGen_6857_ = v_auxDeclNGen_6922_;
                            v_traceState_6858_ = v_traceState_6923_;
                            v_messages_6859_ = v_messages_6924_;
                            v_infoState_6860_ = v_infoState_6925_;
                            v_snapshotTasks_6861_ = v_snapshotTasks_6926_;
                            v___y_6862_ = v___y_6898_;
                            v___y_6863_ = v___y_6899_;
                            v___y_6864_ = v___x_6935_;
                            state = 29;
                            continue;
                        } else {
                            v___x_6936_ = 0usize;
                            v___x_6937_ = lean_usize_of_nat(v___x_6931_);
                            v___x_6938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_6891_, v___x_6936_, v___x_6937_, v___x_6695_);
                            leanh::lean_inc_ref(v___y_6887_);
                            v___x_6939_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(
                                v___y_6887_,
                                v_env_6919_,
                                v___x_6938_,
                            );
                            v___y_6835_ = v___y_6878_;
                            v___y_6836_ = v___y_6879_;
                            v___y_6837_ = v___y_6880_;
                            v___y_6838_ = v___y_6881_;
                            v___y_6839_ = v___y_6883_;
                            v___y_6840_ = v___y_6882_;
                            v___y_6841_ = v___y_6884_;
                            v___y_6842_ = v___y_6885_;
                            v___y_6843_ = v___y_6886_;
                            v___y_6844_ = v___x_6930_;
                            v___y_6845_ = v___y_6888_;
                            v___y_6846_ = v___y_6889_;
                            v___y_6847_ = v___y_6890_;
                            v___y_6848_ = v___y_6891_;
                            v___y_6849_ = v___y_6901_;
                            v___y_6850_ = v___y_6892_;
                            v___y_6851_ = v___y_6893_;
                            v___y_6852_ = v___y_6895_;
                            v___y_6853_ = v___y_6896_;
                            v___y_6854_ = v___y_6897_;
                            v_nextMacroScope_6855_ = v_nextMacroScope_6920_;
                            v_ngen_6856_ = v_ngen_6921_;
                            v_auxDeclNGen_6857_ = v_auxDeclNGen_6922_;
                            v_traceState_6858_ = v_traceState_6923_;
                            v_messages_6859_ = v_messages_6924_;
                            v_infoState_6860_ = v_infoState_6925_;
                            v_snapshotTasks_6861_ = v_snapshotTasks_6926_;
                            v___y_6862_ = v___y_6898_;
                            v___y_6863_ = v___y_6899_;
                            v___y_6864_ = v___x_6939_;
                            state = 29;
                            continue;
                        }
                    } else {
                        v___x_6940_ = 0usize;
                        v___x_6941_ = lean_usize_of_nat(v___x_6931_);
                        v___x_6942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_6891_, v___x_6940_, v___x_6941_, v___x_6695_);
                        leanh::lean_inc_ref(v___y_6887_);
                        v___x_6943_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(
                            v___y_6887_,
                            v_env_6919_,
                            v___x_6942_,
                        );
                        v___y_6835_ = v___y_6878_;
                        v___y_6836_ = v___y_6879_;
                        v___y_6837_ = v___y_6880_;
                        v___y_6838_ = v___y_6881_;
                        v___y_6839_ = v___y_6883_;
                        v___y_6840_ = v___y_6882_;
                        v___y_6841_ = v___y_6884_;
                        v___y_6842_ = v___y_6885_;
                        v___y_6843_ = v___y_6886_;
                        v___y_6844_ = v___x_6930_;
                        v___y_6845_ = v___y_6888_;
                        v___y_6846_ = v___y_6889_;
                        v___y_6847_ = v___y_6890_;
                        v___y_6848_ = v___y_6891_;
                        v___y_6849_ = v___y_6901_;
                        v___y_6850_ = v___y_6892_;
                        v___y_6851_ = v___y_6893_;
                        v___y_6852_ = v___y_6895_;
                        v___y_6853_ = v___y_6896_;
                        v___y_6854_ = v___y_6897_;
                        v_nextMacroScope_6855_ = v_nextMacroScope_6920_;
                        v_ngen_6856_ = v_ngen_6921_;
                        v_auxDeclNGen_6857_ = v_auxDeclNGen_6922_;
                        v_traceState_6858_ = v_traceState_6923_;
                        v_messages_6859_ = v_messages_6924_;
                        v_infoState_6860_ = v_infoState_6925_;
                        v_snapshotTasks_6861_ = v_snapshotTasks_6926_;
                        v___y_6862_ = v___y_6898_;
                        v___y_6863_ = v___y_6899_;
                        v___y_6864_ = v___x_6943_;
                        state = 29;
                        continue;
                    }
                }
            }
            33 => {
                if v___y_6972_ == 0 {
                    v___x_6973_ = lean_st_ref_take(v___y_6967_);
                    v_env_6974_ = leanh::lean_ctor_get(v___x_6973_, 0);
                    v_nextMacroScope_6975_ = leanh::lean_ctor_get(v___x_6973_, 1);
                    v_ngen_6976_ = leanh::lean_ctor_get(v___x_6973_, 2);
                    v_auxDeclNGen_6977_ = leanh::lean_ctor_get(v___x_6973_, 3);
                    v_traceState_6978_ = leanh::lean_ctor_get(v___x_6973_, 4);
                    v_messages_6979_ = leanh::lean_ctor_get(v___x_6973_, 6);
                    v_infoState_6980_ = leanh::lean_ctor_get(v___x_6973_, 7);
                    v_snapshotTasks_6981_ = leanh::lean_ctor_get(v___x_6973_, 8);
                    v_isSharedCheck_6990_ = (!leanh::lean_is_exclusive(v___x_6973_)) as u8;
                    if v_isSharedCheck_6990_ == 0 {
                        v_unused_6991_ = leanh::lean_ctor_get(v___x_6973_, 5);
                        leanh::lean_dec(v_unused_6991_);
                        v___x_6983_ = v___x_6973_;
                        v_isShared_6984_ = v_isSharedCheck_6990_;
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_6981_);
                        leanh::lean_inc(v_infoState_6980_);
                        leanh::lean_inc(v_messages_6979_);
                        leanh::lean_inc(v_traceState_6978_);
                        leanh::lean_inc(v_auxDeclNGen_6977_);
                        leanh::lean_inc(v_ngen_6976_);
                        leanh::lean_inc(v_nextMacroScope_6975_);
                        leanh::lean_inc(v_env_6974_);
                        leanh::lean_dec(v___x_6973_);
                        v___x_6983_ = leanh::lean_box(0);
                        v_isShared_6984_ = v_isSharedCheck_6990_;
                        state = 34;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___y_6967_);
                    v___y_6878_ = v___y_6949_;
                    v___y_6879_ = v___y_6950_;
                    v___y_6880_ = v___y_6951_;
                    v___y_6881_ = v___y_6952_;
                    v___y_6882_ = v___y_6954_;
                    v___y_6883_ = v___y_6953_;
                    v___y_6884_ = v___y_6955_;
                    v___y_6885_ = v___y_6956_;
                    v___y_6886_ = v___y_6957_;
                    v___y_6887_ = v___y_6958_;
                    v___y_6888_ = v___y_6959_;
                    v___y_6889_ = v___y_6960_;
                    v___y_6890_ = v___y_6961_;
                    v___y_6891_ = v___y_6962_;
                    v___y_6892_ = v___y_6963_;
                    v___y_6893_ = v___y_6964_;
                    v___y_6894_ = v___y_6965_;
                    v___y_6895_ = v___y_6966_;
                    v___y_6896_ = v___y_6967_;
                    v___y_6897_ = v___y_6968_;
                    v___y_6898_ = v___y_6970_;
                    v___y_6899_ = v___y_6971_;
                    v___y_6900_ = v___y_6969_;
                    v___y_6901_ = v___y_6967_;
                    state = 30;
                    continue;
                }
            }
            34 => {
                v___x_6985_ = l_Lean_Kernel_enableDiag(v_env_6974_, v___y_6965_);
                leanh::lean_inc_ref(v___y_6971_);
                if v_isShared_6984_ == 0 {
                    leanh::lean_ctor_set(v___x_6983_, 5, v___y_6971_);
                    leanh::lean_ctor_set(v___x_6983_, 0, v___x_6985_);
                    v___x_6987_ = v___x_6983_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6989_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 0, v___x_6985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 1, v_nextMacroScope_6975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 2, v_ngen_6976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 3, v_auxDeclNGen_6977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 4, v_traceState_6978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 5, v___y_6971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 6, v_messages_6979_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 7, v_infoState_6980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 8, v_snapshotTasks_6981_);
                    v___x_6987_ = v_reuseFailAlloc_6989_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_6988_ = lean_st_ref_set(v___y_6967_, v___x_6987_);
                leanh::lean_inc(v___y_6967_);
                v___y_6878_ = v___y_6949_;
                v___y_6879_ = v___y_6950_;
                v___y_6880_ = v___y_6951_;
                v___y_6881_ = v___y_6952_;
                v___y_6882_ = v___y_6954_;
                v___y_6883_ = v___y_6953_;
                v___y_6884_ = v___y_6955_;
                v___y_6885_ = v___y_6956_;
                v___y_6886_ = v___y_6957_;
                v___y_6887_ = v___y_6958_;
                v___y_6888_ = v___y_6959_;
                v___y_6889_ = v___y_6960_;
                v___y_6890_ = v___y_6961_;
                v___y_6891_ = v___y_6962_;
                v___y_6892_ = v___y_6963_;
                v___y_6893_ = v___y_6964_;
                v___y_6894_ = v___y_6965_;
                v___y_6895_ = v___y_6966_;
                v___y_6896_ = v___y_6967_;
                v___y_6897_ = v___y_6968_;
                v___y_6898_ = v___y_6970_;
                v___y_6899_ = v___y_6971_;
                v___y_6900_ = v___y_6969_;
                v___y_6901_ = v___y_6967_;
                state = 30;
                continue;
            }
            36 => {
                if v_isShared_6688_ == 0 {
                    leanh::lean_ctor_set(v___x_6687_, 1, v___y_7003_);
                    leanh::lean_ctor_set(v___x_6687_, 0, v___y_7000_);
                    v___x_7005_ = v___x_6687_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_7100_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7100_, 0, v___y_7000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7100_, 1, v___y_7003_);
                    v___x_7005_ = v_reuseFailAlloc_7100_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_7006_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___y_7002_);
                v___x_7007_ = l_Lean_EnvExtension_setState___redArg(
                    v___y_7002_,
                    v___y_6999_,
                    v___x_7005_,
                    v___x_7006_,
                );
                v___x_7008_ = l_Lean_Environment_header(v___x_7007_);
                v_moduleData_7009_ = leanh::lean_ctor_get(v___x_7008_, 6);
                leanh::lean_inc_ref(v_moduleData_7009_);
                leanh::lean_dec_ref(v___x_7008_);
                v___x_7010_ = lean_array_get_size(v_moduleData_7009_);
                v___x_7011_ = lean_nat_dec_lt(v___y_6998_, v___x_7010_);
                if v___x_7011_ == 0 {
                    leanh::lean_dec_ref(v_moduleData_7009_);
                    leanh::lean_dec_ref(v___x_7007_);
                    leanh::lean_dec(v___y_6998_);
                    leanh::lean_dec(v___y_6997_);
                    leanh::lean_dec(v___y_6996_);
                    leanh::lean_dec_ref(v___x_6702_);
                    leanh::lean_dec(v_fst_6684_);
                    leanh::lean_dec(v_name_6671_);
                    leanh::lean_dec(v_head_6664_);
                    leanh::lean_dec(v_head_6663_);
                    v___x_7012_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_main___closed__21),
                        core::ptr::addr_of_mut!(l_main___closed__21_once),
                        _init_l_main___closed__21,
                    );
                    v___x_7013_ = l_panic___at___00main_spec__5(v___x_7012_);
                    return v___x_7013_;
                } else {
                    v_base_7014_ = leanh::lean_ctor_get(v___x_7007_, 0);
                    leanh::lean_inc_ref(v_base_7014_);
                    v_private_7015_ = leanh::lean_ctor_get(v_base_7014_, 0);
                    leanh::lean_inc(v_private_7015_);
                    v_header_7016_ = leanh::lean_ctor_get(v_private_7015_, 5);
                    leanh::lean_inc_ref(v_header_7016_);
                    v_serverBaseExts_7017_ = leanh::lean_ctor_get(v___x_7007_, 1);
                    v_checked_7018_ = leanh::lean_ctor_get(v___x_7007_, 2);
                    v_asyncConstsMap_7019_ = leanh::lean_ctor_get(v___x_7007_, 3);
                    v_asyncCtx_x3f_7020_ = leanh::lean_ctor_get(v___x_7007_, 4);
                    v_importRealizationCtx_x3f_7021_ = leanh::lean_ctor_get(v___x_7007_, 5);
                    v_localRealizationCtxMap_7022_ = leanh::lean_ctor_get(v___x_7007_, 6);
                    v_allRealizations_7023_ = leanh::lean_ctor_get(v___x_7007_, 7);
                    v_isExporting_7024_ = leanh::lean_ctor_get_uint8(
                        v___x_7007_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    v_isSharedCheck_7098_ = (!leanh::lean_is_exclusive(v___x_7007_)) as u8;
                    if v_isSharedCheck_7098_ == 0 {
                        v_unused_7099_ = leanh::lean_ctor_get(v___x_7007_, 0);
                        leanh::lean_dec(v_unused_7099_);
                        v___x_7026_ = v___x_7007_;
                        v_isShared_7027_ = v_isSharedCheck_7098_;
                        state = 38;
                        continue;
                    } else {
                        leanh::lean_inc(v_allRealizations_7023_);
                        leanh::lean_inc(v_localRealizationCtxMap_7022_);
                        leanh::lean_inc(v_importRealizationCtx_x3f_7021_);
                        leanh::lean_inc(v_asyncCtx_x3f_7020_);
                        leanh::lean_inc(v_asyncConstsMap_7019_);
                        leanh::lean_inc(v_checked_7018_);
                        leanh::lean_inc(v_serverBaseExts_7017_);
                        leanh::lean_dec(v___x_7007_);
                        v___x_7026_ = leanh::lean_box(0);
                        v_isShared_7027_ = v_isSharedCheck_7098_;
                        state = 38;
                        continue;
                    }
                }
            }
            38 => {
                v_public_7028_ = leanh::lean_ctor_get(v_base_7014_, 1);
                v_isSharedCheck_7096_ = (!leanh::lean_is_exclusive(v_base_7014_)) as u8;
                if v_isSharedCheck_7096_ == 0 {
                    v_unused_7097_ = leanh::lean_ctor_get(v_base_7014_, 0);
                    leanh::lean_dec(v_unused_7097_);
                    v___x_7030_ = v_base_7014_;
                    v_isShared_7031_ = v_isSharedCheck_7096_;
                    state = 39;
                    continue;
                } else {
                    leanh::lean_inc(v_public_7028_);
                    leanh::lean_dec(v_base_7014_);
                    v___x_7030_ = leanh::lean_box(0);
                    v_isShared_7031_ = v_isSharedCheck_7096_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v_constants_7032_ = leanh::lean_ctor_get(v_private_7015_, 0);
                v_quotInit_7033_ = leanh::lean_ctor_get_uint8(
                    v_private_7015_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_diagnostics_7034_ = leanh::lean_ctor_get(v_private_7015_, 1);
                v_const2ModIdx_7035_ = leanh::lean_ctor_get(v_private_7015_, 2);
                v_extensions_7036_ = leanh::lean_ctor_get(v_private_7015_, 3);
                v_irBaseExts_7037_ = leanh::lean_ctor_get(v_private_7015_, 4);
                v_isSharedCheck_7094_ = (!leanh::lean_is_exclusive(v_private_7015_)) as u8;
                if v_isSharedCheck_7094_ == 0 {
                    v_unused_7095_ = leanh::lean_ctor_get(v_private_7015_, 5);
                    leanh::lean_dec(v_unused_7095_);
                    v___x_7039_ = v_private_7015_;
                    v_isShared_7040_ = v_isSharedCheck_7094_;
                    state = 40;
                    continue;
                } else {
                    leanh::lean_inc(v_irBaseExts_7037_);
                    leanh::lean_inc(v_extensions_7036_);
                    leanh::lean_inc(v_const2ModIdx_7035_);
                    leanh::lean_inc(v_diagnostics_7034_);
                    leanh::lean_inc(v_constants_7032_);
                    leanh::lean_dec(v_private_7015_);
                    v___x_7039_ = leanh::lean_box(0);
                    v_isShared_7040_ = v_isSharedCheck_7094_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v_trustLevel_7041_ = leanh::lean_ctor_get_uint32(
                    v_header_7016_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_mainModule_7042_ = leanh::lean_ctor_get(v_header_7016_, 0);
                v_isModule_7043_ = leanh::lean_ctor_get_uint8(
                    v_header_7016_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                v_regions_7044_ = leanh::lean_ctor_get(v_header_7016_, 2);
                v_modules_7045_ = leanh::lean_ctor_get(v_header_7016_, 3);
                v_moduleName2Idx_7046_ = leanh::lean_ctor_get(v_header_7016_, 4);
                v_importAllModules_7047_ = leanh::lean_ctor_get(v_header_7016_, 5);
                v_moduleData_7048_ = leanh::lean_ctor_get(v_header_7016_, 6);
                v_isSharedCheck_7092_ = (!leanh::lean_is_exclusive(v_header_7016_)) as u8;
                if v_isSharedCheck_7092_ == 0 {
                    v_unused_7093_ = leanh::lean_ctor_get(v_header_7016_, 1);
                    leanh::lean_dec(v_unused_7093_);
                    v___x_7050_ = v_header_7016_;
                    v_isShared_7051_ = v_isSharedCheck_7092_;
                    state = 41;
                    continue;
                } else {
                    leanh::lean_inc(v_moduleData_7048_);
                    leanh::lean_inc(v_importAllModules_7047_);
                    leanh::lean_inc(v_moduleName2Idx_7046_);
                    leanh::lean_inc(v_modules_7045_);
                    leanh::lean_inc(v_regions_7044_);
                    leanh::lean_inc(v_mainModule_7042_);
                    leanh::lean_dec(v_header_7016_);
                    v___x_7050_ = leanh::lean_box(0);
                    v_isShared_7051_ = v_isSharedCheck_7092_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v___x_7052_ = lean_array_fget(v_moduleData_7009_, v___y_6998_);
                leanh::lean_dec_ref(v_moduleData_7009_);
                v_imports_7053_ = leanh::lean_ctor_get(v___x_7052_, 0);
                leanh::lean_inc_ref(v_imports_7053_);
                leanh::lean_dec(v___x_7052_);
                if v_isShared_7051_ == 0 {
                    leanh::lean_ctor_set(v___x_7050_, 1, v_imports_7053_);
                    v___x_7055_ = v___x_7050_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_7091_ = leanh::lean_alloc_ctor(0, 7, (5) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 0, v_mainModule_7042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 1, v_imports_7053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 2, v_regions_7044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 3, v_modules_7045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 4, v_moduleName2Idx_7046_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7091_,
                        5,
                        v_importAllModules_7047_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 6, v_moduleData_7048_);
                    leanh::lean_ctor_set_uint32(
                        v_reuseFailAlloc_7091_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v_trustLevel_7041_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7091_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                        v_isModule_7043_,
                    );
                    v___x_7055_ = v_reuseFailAlloc_7091_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_7040_ == 0 {
                    leanh::lean_ctor_set(v___x_7039_, 5, v___x_7055_);
                    v___x_7057_ = v___x_7039_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_7090_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 0, v_constants_7032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 1, v_diagnostics_7034_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 2, v_const2ModIdx_7035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 3, v_extensions_7036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 4, v_irBaseExts_7037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 5, v___x_7055_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7090_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_quotInit_7033_,
                    );
                    v___x_7057_ = v_reuseFailAlloc_7090_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_7031_ == 0 {
                    leanh::lean_ctor_set(v___x_7030_, 0, v___x_7057_);
                    v___x_7059_ = v___x_7030_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_7089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 0, v___x_7057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 1, v_public_7028_);
                    v___x_7059_ = v_reuseFailAlloc_7089_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_7027_ == 0 {
                    leanh::lean_ctor_set(v___x_7026_, 0, v___x_7059_);
                    v___x_7061_ = v___x_7026_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_7088_ = leanh::lean_alloc_ctor(0, 8, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 0, v___x_7059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 1, v_serverBaseExts_7017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 2, v_checked_7018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 3, v_asyncConstsMap_7019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 4, v_asyncCtx_x3f_7020_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7088_,
                        5,
                        v_importRealizationCtx_x3f_7021_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7088_,
                        6,
                        v_localRealizationCtxMap_7022_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 7, v_allRealizations_7023_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7088_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                        v_isExporting_7024_,
                    );
                    v___x_7061_ = v_reuseFailAlloc_7088_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                v___x_7062_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
                v___x_7063_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_6696_,
                    v___x_7062_,
                    v___x_7061_,
                    v___y_6998_,
                    v___y_7001_,
                );
                leanh::lean_dec(v___y_6998_);
                v___x_7064_ = l_Lean_firstFrontendMacroScope;
                v___x_7065_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__22),
                    core::ptr::addr_of_mut!(l_main___closed__22_once),
                    _init_l_main___closed__22,
                );
                v___x_7066_ = l_main___closed__25;
                leanh::lean_inc_n(v___y_6997_, 3);
                v___x_7067_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_7067_, 0, v___y_6997_);
                leanh::lean_ctor_set(v___x_7067_, 1, v___x_6994_);
                leanh::lean_ctor_set(v___x_7067_, 2, v___x_6682_);
                v___x_7068_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__26),
                    core::ptr::addr_of_mut!(l_main___closed__26_once),
                    _init_l_main___closed__26,
                );
                v___x_7069_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__29),
                    core::ptr::addr_of_mut!(l_main___closed__29_once),
                    _init_l_main___closed__29,
                );
                v___x_7070_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__30),
                    core::ptr::addr_of_mut!(l_main___closed__30_once),
                    _init_l_main___closed__30,
                );
                v___x_7071_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__31),
                    core::ptr::addr_of_mut!(l_main___closed__31_once),
                    _init_l_main___closed__31,
                );
                v___x_7072_ = l_main___closed__32;
                leanh::lean_inc_ref(v___x_7067_);
                v___x_7073_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_7073_, 0, v___x_7061_);
                leanh::lean_ctor_set(v___x_7073_, 1, v___x_7065_);
                leanh::lean_ctor_set(v___x_7073_, 2, v___x_7066_);
                leanh::lean_ctor_set(v___x_7073_, 3, v___x_7067_);
                leanh::lean_ctor_set(v___x_7073_, 4, v___x_7068_);
                leanh::lean_ctor_set(v___x_7073_, 5, v___x_7069_);
                leanh::lean_ctor_set(v___x_7073_, 6, v___x_7070_);
                leanh::lean_ctor_set(v___x_7073_, 7, v___x_7071_);
                leanh::lean_ctor_set(v___x_7073_, 8, v___x_7072_);
                v___x_7074_ = lean_st_mk_ref(v___x_7073_);
                v___x_7075_ = l_Lean_inheritedTraceOptions;
                v___x_7076_ = lean_st_ref_get(v___x_7075_);
                v___x_7077_ = lean_st_ref_get(v___x_7074_);
                v___x_7078_ = l_Lean_instInhabitedFileMap_default;
                v___x_7079_ = leanh::lean_unsigned_to_nat(1000);
                v___x_7080_ = leanh::lean_box(0);
                v___x_7081_ = l_Lean_Core_getMaxHeartbeats(v___x_6702_);
                v___x_7082_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_6702_);
                leanh::lean_inc(v_head_6663_);
                v___x_7083_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_7083_, 0, v_head_6663_);
                leanh::lean_ctor_set(v___x_7083_, 1, v___x_7078_);
                leanh::lean_ctor_set(v___x_7083_, 2, v___x_6702_);
                leanh::lean_ctor_set(v___x_7083_, 3, v___x_6701_);
                leanh::lean_ctor_set(v___x_7083_, 4, v___x_7079_);
                leanh::lean_ctor_set(v___x_7083_, 5, v___x_7080_);
                leanh::lean_ctor_set(v___x_7083_, 6, v___y_6997_);
                leanh::lean_ctor_set(v___x_7083_, 7, v___x_6682_);
                leanh::lean_ctor_set(v___x_7083_, 8, v___x_6701_);
                leanh::lean_ctor_set(v___x_7083_, 9, v___x_7081_);
                leanh::lean_ctor_set(v___x_7083_, 10, v___y_6997_);
                leanh::lean_ctor_set(v___x_7083_, 11, v___x_7064_);
                leanh::lean_ctor_set(v___x_7083_, 12, v___x_7082_);
                leanh::lean_ctor_set(v___x_7083_, 13, v___x_7076_);
                leanh::lean_ctor_set_uint8(
                    v___x_7083_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_6673_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7083_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___x_6673_,
                );
                v_env_7084_ = leanh::lean_ctor_get(v___x_7077_, 0);
                leanh::lean_inc_ref(v_env_7084_);
                leanh::lean_dec(v___x_7077_);
                v___x_7085_ = l_Lean_diagnostics;
                v___x_7086_ = l_Lean_Option_get___at___00main_spec__8(v___x_6702_, v___x_7085_);
                v___x_7087_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_7084_);
                leanh::lean_dec_ref(v_env_7084_);
                if v___x_7087_ == 0 {
                    if v___x_7086_ == 0 {
                        v___y_6949_ = v___y_6996_;
                        v___y_6950_ = v___x_7080_;
                        v___y_6951_ = v___x_7078_;
                        v___y_6952_ = v___x_7011_;
                        v___y_6953_ = v___x_7064_;
                        v___y_6954_ = v___x_7082_;
                        v___y_6955_ = v___x_6682_;
                        v___y_6956_ = v___x_7075_;
                        v___y_6957_ = v___x_7069_;
                        v___y_6958_ = v___x_7062_;
                        v___y_6959_ = v___y_6997_;
                        v___y_6960_ = v___x_7071_;
                        v___y_6961_ = v___x_7066_;
                        v___y_6962_ = v___x_7063_;
                        v___y_6963_ = v___x_7065_;
                        v___y_6964_ = v___x_7072_;
                        v___y_6965_ = v___x_7086_;
                        v___y_6966_ = v___x_7067_;
                        v___y_6967_ = v___x_7074_;
                        v___y_6968_ = v___x_7070_;
                        v___y_6969_ = v___x_7083_;
                        v___y_6970_ = v___x_7068_;
                        v___y_6971_ = v___x_7069_;
                        v___y_6972_ = v___x_7011_;
                        state = 33;
                        continue;
                    } else {
                        v___y_6949_ = v___y_6996_;
                        v___y_6950_ = v___x_7080_;
                        v___y_6951_ = v___x_7078_;
                        v___y_6952_ = v___x_7011_;
                        v___y_6953_ = v___x_7064_;
                        v___y_6954_ = v___x_7082_;
                        v___y_6955_ = v___x_6682_;
                        v___y_6956_ = v___x_7075_;
                        v___y_6957_ = v___x_7069_;
                        v___y_6958_ = v___x_7062_;
                        v___y_6959_ = v___y_6997_;
                        v___y_6960_ = v___x_7071_;
                        v___y_6961_ = v___x_7066_;
                        v___y_6962_ = v___x_7063_;
                        v___y_6963_ = v___x_7065_;
                        v___y_6964_ = v___x_7072_;
                        v___y_6965_ = v___x_7086_;
                        v___y_6966_ = v___x_7067_;
                        v___y_6967_ = v___x_7074_;
                        v___y_6968_ = v___x_7070_;
                        v___y_6969_ = v___x_7083_;
                        v___y_6970_ = v___x_7068_;
                        v___y_6971_ = v___x_7069_;
                        v___y_6972_ = v___x_7087_;
                        state = 33;
                        continue;
                    }
                } else {
                    v___y_6949_ = v___y_6996_;
                    v___y_6950_ = v___x_7080_;
                    v___y_6951_ = v___x_7078_;
                    v___y_6952_ = v___x_7011_;
                    v___y_6953_ = v___x_7064_;
                    v___y_6954_ = v___x_7082_;
                    v___y_6955_ = v___x_6682_;
                    v___y_6956_ = v___x_7075_;
                    v___y_6957_ = v___x_7069_;
                    v___y_6958_ = v___x_7062_;
                    v___y_6959_ = v___y_6997_;
                    v___y_6960_ = v___x_7071_;
                    v___y_6961_ = v___x_7066_;
                    v___y_6962_ = v___x_7063_;
                    v___y_6963_ = v___x_7065_;
                    v___y_6964_ = v___x_7072_;
                    v___y_6965_ = v___x_7086_;
                    v___y_6966_ = v___x_7067_;
                    v___y_6967_ = v___x_7074_;
                    v___y_6968_ = v___x_7070_;
                    v___y_6969_ = v___x_7083_;
                    v___y_6970_ = v___x_7068_;
                    v___y_6971_ = v___x_7069_;
                    v___y_6972_ = v___x_7086_;
                    state = 33;
                    continue;
                }
            }
            46 => {
                v___x_7107_ = l_Lean_IR_declMapExt;
                v_toEnvExtension_7108_ = leanh::lean_ctor_get(v___x_7107_, 0);
                v_asyncMode_7109_ = leanh::lean_ctor_get(v_toEnvExtension_7108_, 2);
                leanh::lean_inc(v___y_7104_);
                leanh::lean_inc_ref(v___y_7106_);
                v___x_7110_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_6693_,
                        v_toEnvExtension_7108_,
                        v___y_7106_,
                        v_asyncMode_7109_,
                        v___y_7104_,
                    );
                v_importedEntries_7111_ = leanh::lean_ctor_get(v___x_7110_, 0);
                leanh::lean_inc_ref(v_importedEntries_7111_);
                v_state_7112_ = leanh::lean_ctor_get(v___x_7110_, 1);
                leanh::lean_inc(v_state_7112_);
                leanh::lean_dec(v___x_7110_);
                v___x_7113_ =
                    lean_array_get_borrowed(v___x_6694_, v_importedEntries_7111_, v___y_7103_);
                v___x_7114_ = lean_array_get_size(v___x_7113_);
                v___x_7115_ = lean_nat_dec_lt(v___x_6701_, v___x_7114_);
                if v___x_7115_ == 0 {
                    v___y_6996_ = v___y_7102_;
                    v___y_6997_ = v___y_7104_;
                    v___y_6998_ = v___y_7103_;
                    v___y_6999_ = v___y_7106_;
                    v___y_7000_ = v_importedEntries_7111_;
                    v___y_7001_ = v___y_7105_;
                    v___y_7002_ = v_toEnvExtension_7108_;
                    v___y_7003_ = v_state_7112_;
                    state = 36;
                    continue;
                } else {
                    v___x_7116_ = lean_nat_dec_le(v___x_7114_, v___x_7114_);
                    if v___x_7116_ == 0 {
                        if v___x_7115_ == 0 {
                            v___y_6996_ = v___y_7102_;
                            v___y_6997_ = v___y_7104_;
                            v___y_6998_ = v___y_7103_;
                            v___y_6999_ = v___y_7106_;
                            v___y_7000_ = v_importedEntries_7111_;
                            v___y_7001_ = v___y_7105_;
                            v___y_7002_ = v_toEnvExtension_7108_;
                            v___y_7003_ = v_state_7112_;
                            state = 36;
                            continue;
                        } else {
                            v___x_7117_ = 0usize;
                            v___x_7118_ = lean_usize_of_nat(v___x_7114_);
                            leanh::lean_inc_ref(v___y_7106_);
                            v___x_7119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_7106_, v___x_7113_, v___x_7117_, v___x_7118_, v_state_7112_);
                            v___y_6996_ = v___y_7102_;
                            v___y_6997_ = v___y_7104_;
                            v___y_6998_ = v___y_7103_;
                            v___y_6999_ = v___y_7106_;
                            v___y_7000_ = v_importedEntries_7111_;
                            v___y_7001_ = v___y_7105_;
                            v___y_7002_ = v_toEnvExtension_7108_;
                            v___y_7003_ = v___x_7119_;
                            state = 36;
                            continue;
                        }
                    } else {
                        v___x_7120_ = 0usize;
                        v___x_7121_ = lean_usize_of_nat(v___x_7114_);
                        leanh::lean_inc_ref(v___y_7106_);
                        v___x_7122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_7106_, v___x_7113_, v___x_7120_, v___x_7121_, v_state_7112_);
                        v___y_6996_ = v___y_7102_;
                        v___y_6997_ = v___y_7104_;
                        v___y_6998_ = v___y_7103_;
                        v___y_6999_ = v___y_7106_;
                        v___y_7000_ = v_importedEntries_7111_;
                        v___y_7001_ = v___y_7105_;
                        v___y_7002_ = v_toEnvExtension_7108_;
                        v___y_7003_ = v___x_7122_;
                        state = 36;
                        continue;
                    }
                }
            }
            47 => {
                v___x_7131_ = lean_nat_dec_lt(v___x_6701_, v___y_7127_);
                if v___x_7131_ == 0 {
                    leanh::lean_dec_ref(v___y_7129_);
                    leanh::lean_dec(v___y_7127_);
                    v___y_7102_ = v___y_7124_;
                    v___y_7103_ = v___y_7126_;
                    v___y_7104_ = v___y_7125_;
                    v___y_7105_ = v___y_7128_;
                    v___y_7106_ = v___y_7130_;
                    state = 46;
                    continue;
                } else {
                    v___x_7132_ = lean_nat_dec_le(v___y_7127_, v___y_7127_);
                    if v___x_7132_ == 0 {
                        if v___x_7131_ == 0 {
                            leanh::lean_dec_ref(v___y_7129_);
                            leanh::lean_dec(v___y_7127_);
                            v___y_7102_ = v___y_7124_;
                            v___y_7103_ = v___y_7126_;
                            v___y_7104_ = v___y_7125_;
                            v___y_7105_ = v___y_7128_;
                            v___y_7106_ = v___y_7130_;
                            state = 46;
                            continue;
                        } else {
                            v___x_7133_ = 0usize;
                            v___x_7134_ = lean_usize_of_nat(v___y_7127_);
                            leanh::lean_dec(v___y_7127_);
                            v___x_7135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_7129_, v___x_7133_, v___x_7134_, v___y_7130_);
                            leanh::lean_dec_ref(v___y_7129_);
                            v___y_7102_ = v___y_7124_;
                            v___y_7103_ = v___y_7126_;
                            v___y_7104_ = v___y_7125_;
                            v___y_7105_ = v___y_7128_;
                            v___y_7106_ = v___x_7135_;
                            state = 46;
                            continue;
                        }
                    } else {
                        v___x_7136_ = 0usize;
                        v___x_7137_ = lean_usize_of_nat(v___y_7127_);
                        leanh::lean_dec(v___y_7127_);
                        v___x_7138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_7129_, v___x_7136_, v___x_7137_, v___y_7130_);
                        leanh::lean_dec_ref(v___y_7129_);
                        v___y_7102_ = v___y_7124_;
                        v___y_7103_ = v___y_7126_;
                        v___y_7104_ = v___y_7125_;
                        v___y_7105_ = v___y_7128_;
                        v___y_7106_ = v___x_7138_;
                        state = 46;
                        continue;
                    }
                }
            }
            48 => {
                v___x_7146_ = lean_array_get_size(v___y_7145_);
                v___x_7147_ = lean_nat_dec_lt(v___x_6701_, v___x_7146_);
                if v___x_7147_ == 0 {
                    v___y_7124_ = v___y_7140_;
                    v___y_7125_ = v___y_7143_;
                    v___y_7126_ = v___y_7141_;
                    v___y_7127_ = v___x_7146_;
                    v___y_7128_ = v___y_7144_;
                    v___y_7129_ = v___y_7145_;
                    v___y_7130_ = v___y_7142_;
                    state = 47;
                    continue;
                } else {
                    v___x_7148_ = lean_nat_dec_le(v___x_7146_, v___x_7146_);
                    if v___x_7148_ == 0 {
                        if v___x_7147_ == 0 {
                            v___y_7124_ = v___y_7140_;
                            v___y_7125_ = v___y_7143_;
                            v___y_7126_ = v___y_7141_;
                            v___y_7127_ = v___x_7146_;
                            v___y_7128_ = v___y_7144_;
                            v___y_7129_ = v___y_7145_;
                            v___y_7130_ = v___y_7142_;
                            state = 47;
                            continue;
                        } else {
                            v___x_7149_ = 0usize;
                            v___x_7150_ = lean_usize_of_nat(v___x_7146_);
                            v___x_7151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_7145_, v___x_7149_, v___x_7150_, v___y_7142_);
                            v___y_7124_ = v___y_7140_;
                            v___y_7125_ = v___y_7143_;
                            v___y_7126_ = v___y_7141_;
                            v___y_7127_ = v___x_7146_;
                            v___y_7128_ = v___y_7144_;
                            v___y_7129_ = v___y_7145_;
                            v___y_7130_ = v___x_7151_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v___x_7152_ = 0usize;
                        v___x_7153_ = lean_usize_of_nat(v___x_7146_);
                        v___x_7154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_7145_, v___x_7152_, v___x_7153_, v___y_7142_);
                        v___y_7124_ = v___y_7140_;
                        v___y_7125_ = v___y_7143_;
                        v___y_7126_ = v___y_7141_;
                        v___y_7127_ = v___x_7146_;
                        v___y_7128_ = v___y_7144_;
                        v___y_7129_ = v___y_7145_;
                        v___y_7130_ = v___x_7154_;
                        state = 47;
                        continue;
                    }
                }
            }
            49 => {
                v___x_7160_ = l_Lean_instInhabitedImportState_default;
                v___x_7161_ = leanh::lean_box((v___x_7157_) as usize);
                v___x_7162_ = leanh::lean_box((v___y_7159_) as usize);
                v___x_7163_ = leanh::lean_box((v___x_6698_) as usize);
                v___x_7164_ = leanh::lean_box((v___x_6673_) as usize);
                leanh::lean_inc_ref(v___x_6702_);
                leanh::lean_inc(v_name_6671_);
                v___f_7165_ = leanh::lean_alloc_closure(
                    l_main___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    9,
                );
                leanh::lean_closure_set(v___f_7165_, 0, v___x_7160_);
                leanh::lean_closure_set(v___f_7165_, 1, v___x_7156_);
                leanh::lean_closure_set(v___f_7165_, 2, v___x_7161_);
                leanh::lean_closure_set(v___f_7165_, 3, v___x_6695_);
                leanh::lean_closure_set(v___f_7165_, 4, v___x_7162_);
                leanh::lean_closure_set(v___f_7165_, 5, v_name_6671_);
                leanh::lean_closure_set(v___f_7165_, 6, v___x_6702_);
                leanh::lean_closure_set(v___f_7165_, 7, v___x_7163_);
                leanh::lean_closure_set(v___f_7165_, 8, v___x_7164_);
                v___x_7166_ = leanh::lean_alloc_closure(
                    l_Lean_withImporting___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___x_7166_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7166_, 1, v___f_7165_);
                v___x_7167_ = leanh::lean_box(0);
                v___x_7168_ = l_Lean_profileitIOUnsafe___redArg(
                    v___x_6992_,
                    v___x_6702_,
                    v___x_7166_,
                    v___x_7167_,
                );
                if leanh::lean_obj_tag(v___x_7168_) == 0 {
                    v_a_7169_ = leanh::lean_ctor_get(v___x_7168_, 0);
                    leanh::lean_inc(v_a_7169_);
                    leanh::lean_dec_ref_known(v___x_7168_, 1);
                    v___x_7170_ = l_Lean_Compiler_CSimp_ext;
                    v_ext_7171_ = leanh::lean_ctor_get(v___x_7170_, 1);
                    leanh::lean_inc(v_name_6671_);
                    v___x_7172_ = l_Lean_Environment_setMainModule(v_a_7169_, v_name_6671_);
                    leanh::lean_inc_ref(v_ext_7171_);
                    v___x_7173_ = l_main___elam__0___redArg(
                        v___x_7167_,
                        v___x_6689_,
                        v_ext_7171_,
                        v___x_7172_,
                    );
                    if leanh::lean_obj_tag(v___x_7173_) == 0 {
                        v_a_7174_ = leanh::lean_ctor_get(v___x_7173_, 0);
                        leanh::lean_inc(v_a_7174_);
                        leanh::lean_dec_ref_known(v___x_7173_, 1);
                        v___x_7175_ = l_Lean_Meta_instanceExtension;
                        v_ext_7176_ = leanh::lean_ctor_get(v___x_7175_, 1);
                        leanh::lean_inc_ref(v_ext_7176_);
                        v___x_7177_ = l_main___elam__0___redArg(
                            v___x_7167_,
                            v___x_6689_,
                            v_ext_7176_,
                            v_a_7174_,
                        );
                        if leanh::lean_obj_tag(v___x_7177_) == 0 {
                            v_a_7178_ = leanh::lean_ctor_get(v___x_7177_, 0);
                            leanh::lean_inc(v_a_7178_);
                            leanh::lean_dec_ref_known(v___x_7177_, 1);
                            v___x_7179_ = l_Lean_classExtension;
                            v___x_7180_ = l_main___elam__0___redArg(
                                v___x_7167_,
                                v___x_6690_,
                                v___x_7179_,
                                v_a_7178_,
                            );
                            if leanh::lean_obj_tag(v___x_7180_) == 0 {
                                v_a_7181_ = leanh::lean_ctor_get(v___x_7180_, 0);
                                leanh::lean_inc(v_a_7181_);
                                leanh::lean_dec_ref_known(v___x_7180_, 1);
                                v___x_7182_ = l_Lean_Meta_Match_Extension_extension;
                                v___x_7183_ = l_main___elam__0___redArg(
                                    v___x_7167_,
                                    v___x_6691_,
                                    v___x_7182_,
                                    v_a_7181_,
                                );
                                if leanh::lean_obj_tag(v___x_7183_) == 0 {
                                    v_a_7184_ = leanh::lean_ctor_get(v___x_7183_, 0);
                                    v_isSharedCheck_7212_ =
                                        (!leanh::lean_is_exclusive(v___x_7183_)) as u8;
                                    if v_isSharedCheck_7212_ == 0 {
                                        v___x_7186_ = v___x_7183_;
                                        v_isShared_7187_ = v_isSharedCheck_7212_;
                                        state = 50;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7184_);
                                        leanh::lean_dec(v___x_7183_);
                                        v___x_7186_ = leanh::lean_box(0);
                                        v_isShared_7187_ = v_isSharedCheck_7212_;
                                        state = 50;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_6702_);
                                    leanh::lean_del_object(v___x_6687_);
                                    leanh::lean_dec(v_fst_6684_);
                                    leanh::lean_dec(v_name_6671_);
                                    leanh::lean_dec(v_head_6664_);
                                    leanh::lean_dec(v_head_6663_);
                                    v_a_7213_ = leanh::lean_ctor_get(v___x_7183_, 0);
                                    v_isSharedCheck_7220_ =
                                        (!leanh::lean_is_exclusive(v___x_7183_)) as u8;
                                    if v_isSharedCheck_7220_ == 0 {
                                        v___x_7215_ = v___x_7183_;
                                        v_isShared_7216_ = v_isSharedCheck_7220_;
                                        state = 52;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7213_);
                                        leanh::lean_dec(v___x_7183_);
                                        v___x_7215_ = leanh::lean_box(0);
                                        v_isShared_7216_ = v_isSharedCheck_7220_;
                                        state = 52;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_6702_);
                                leanh::lean_del_object(v___x_6687_);
                                leanh::lean_dec(v_fst_6684_);
                                leanh::lean_dec(v_name_6671_);
                                leanh::lean_dec(v_head_6664_);
                                leanh::lean_dec(v_head_6663_);
                                v_a_7221_ = leanh::lean_ctor_get(v___x_7180_, 0);
                                v_isSharedCheck_7228_ =
                                    (!leanh::lean_is_exclusive(v___x_7180_)) as u8;
                                if v_isSharedCheck_7228_ == 0 {
                                    v___x_7223_ = v___x_7180_;
                                    v_isShared_7224_ = v_isSharedCheck_7228_;
                                    state = 54;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7221_);
                                    leanh::lean_dec(v___x_7180_);
                                    v___x_7223_ = leanh::lean_box(0);
                                    v_isShared_7224_ = v_isSharedCheck_7228_;
                                    state = 54;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_6702_);
                            leanh::lean_del_object(v___x_6687_);
                            leanh::lean_dec(v_fst_6684_);
                            leanh::lean_dec(v_name_6671_);
                            leanh::lean_dec(v_head_6664_);
                            leanh::lean_dec(v_head_6663_);
                            v_a_7229_ = leanh::lean_ctor_get(v___x_7177_, 0);
                            v_isSharedCheck_7236_ =
                                (!leanh::lean_is_exclusive(v___x_7177_)) as u8;
                            if v_isSharedCheck_7236_ == 0 {
                                v___x_7231_ = v___x_7177_;
                                v_isShared_7232_ = v_isSharedCheck_7236_;
                                state = 56;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7229_);
                                leanh::lean_dec(v___x_7177_);
                                v___x_7231_ = leanh::lean_box(0);
                                v_isShared_7232_ = v_isSharedCheck_7236_;
                                state = 56;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_6702_);
                        leanh::lean_del_object(v___x_6687_);
                        leanh::lean_dec(v_fst_6684_);
                        leanh::lean_dec(v_name_6671_);
                        leanh::lean_dec(v_head_6664_);
                        leanh::lean_dec(v_head_6663_);
                        v_a_7237_ = leanh::lean_ctor_get(v___x_7173_, 0);
                        v_isSharedCheck_7244_ =
                            (!leanh::lean_is_exclusive(v___x_7173_)) as u8;
                        if v_isSharedCheck_7244_ == 0 {
                            v___x_7239_ = v___x_7173_;
                            v_isShared_7240_ = v_isSharedCheck_7244_;
                            state = 58;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7237_);
                            leanh::lean_dec(v___x_7173_);
                            v___x_7239_ = leanh::lean_box(0);
                            v_isShared_7240_ = v_isSharedCheck_7244_;
                            state = 58;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6702_);
                    leanh::lean_del_object(v___x_6687_);
                    leanh::lean_dec(v_fst_6684_);
                    leanh::lean_dec(v_name_6671_);
                    leanh::lean_dec(v_head_6664_);
                    leanh::lean_dec(v_head_6663_);
                    v_a_7245_ = leanh::lean_ctor_get(v___x_7168_, 0);
                    v_isSharedCheck_7252_ = (!leanh::lean_is_exclusive(v___x_7168_)) as u8;
                    if v_isSharedCheck_7252_ == 0 {
                        v___x_7247_ = v___x_7168_;
                        v_isShared_7248_ = v_isSharedCheck_7252_;
                        state = 60;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7245_);
                        leanh::lean_dec(v___x_7168_);
                        v___x_7247_ = leanh::lean_box(0);
                        v_isShared_7248_ = v_isSharedCheck_7252_;
                        state = 60;
                        continue;
                    }
                }
            }
            50 => {
                v___x_7188_ = l_Lean_Environment_getModuleIdx_x3f(v_a_7184_, v_name_6671_);
                if leanh::lean_obj_tag(v___x_7188_) == 1 {
                    leanh::lean_del_object(v___x_7186_);
                    v_val_7189_ = leanh::lean_ctor_get(v___x_7188_, 0);
                    leanh::lean_inc(v_val_7189_);
                    leanh::lean_dec_ref_known(v___x_7188_, 1);
                    v___x_7190_ = l_Lean_Compiler_LCNF_impureSigExt;
                    v___x_7191_ = 0;
                    v___x_7192_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                        v___x_6692_,
                        v___x_7190_,
                        v_a_7184_,
                        v_val_7189_,
                        v___x_7191_,
                    );
                    v___x_7193_ = lean_array_get_size(v___x_7192_);
                    v___x_7194_ = l_main___closed__33;
                    v___x_7195_ = lean_nat_dec_lt(v___x_6701_, v___x_7193_);
                    if v___x_7195_ == 0 {
                        leanh::lean_dec_ref(v___x_7192_);
                        v___y_7140_ = v___x_7167_;
                        v___y_7141_ = v_val_7189_;
                        v___y_7142_ = v_a_7184_;
                        v___y_7143_ = v___x_7167_;
                        v___y_7144_ = v___x_7191_;
                        v___y_7145_ = v___x_7194_;
                        state = 48;
                        continue;
                    } else {
                        v___x_7196_ = lean_nat_dec_le(v___x_7193_, v___x_7193_);
                        if v___x_7196_ == 0 {
                            if v___x_7195_ == 0 {
                                leanh::lean_dec_ref(v___x_7192_);
                                v___y_7140_ = v___x_7167_;
                                v___y_7141_ = v_val_7189_;
                                v___y_7142_ = v_a_7184_;
                                v___y_7143_ = v___x_7167_;
                                v___y_7144_ = v___x_7191_;
                                v___y_7145_ = v___x_7194_;
                                state = 48;
                                continue;
                            } else {
                                v___x_7197_ = 0usize;
                                v___x_7198_ = lean_usize_of_nat(v___x_7193_);
                                leanh::lean_inc(v_a_7184_);
                                v___x_7199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_7184_, v___x_7192_, v___x_7197_, v___x_7198_, v___x_7194_);
                                leanh::lean_dec_ref(v___x_7192_);
                                v___y_7140_ = v___x_7167_;
                                v___y_7141_ = v_val_7189_;
                                v___y_7142_ = v_a_7184_;
                                v___y_7143_ = v___x_7167_;
                                v___y_7144_ = v___x_7191_;
                                v___y_7145_ = v___x_7199_;
                                state = 48;
                                continue;
                            }
                        } else {
                            v___x_7200_ = 0usize;
                            v___x_7201_ = lean_usize_of_nat(v___x_7193_);
                            leanh::lean_inc(v_a_7184_);
                            v___x_7202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_7184_, v___x_7192_, v___x_7200_, v___x_7201_, v___x_7194_);
                            leanh::lean_dec_ref(v___x_7192_);
                            v___y_7140_ = v___x_7167_;
                            v___y_7141_ = v_val_7189_;
                            v___y_7142_ = v_a_7184_;
                            v___y_7143_ = v___x_7167_;
                            v___y_7144_ = v___x_7191_;
                            v___y_7145_ = v___x_7202_;
                            state = 48;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_7188_);
                    leanh::lean_dec(v_a_7184_);
                    leanh::lean_dec_ref(v___x_6702_);
                    leanh::lean_del_object(v___x_6687_);
                    leanh::lean_dec(v_fst_6684_);
                    leanh::lean_dec(v_head_6664_);
                    leanh::lean_dec(v_head_6663_);
                    v___x_7203_ = l_main___closed__34;
                    v___x_7204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_6671_,
                        v___x_6698_,
                    );
                    v___x_7205_ = lean_string_append(v___x_7203_, v___x_7204_);
                    leanh::lean_dec_ref(v___x_7204_);
                    v___x_7206_ = l_main___closed__35;
                    v___x_7207_ = lean_string_append(v___x_7205_, v___x_7206_);
                    v___x_7208_ = lean_mk_io_user_error(v___x_7207_);
                    if v_isShared_7187_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_7186_, 1);
                        leanh::lean_ctor_set(v___x_7186_, 0, v___x_7208_);
                        v___x_7210_ = v___x_7186_;
                        state = 51;
                        continue;
                    } else {
                        v_reuseFailAlloc_7211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7211_, 0, v___x_7208_);
                        v___x_7210_ = v_reuseFailAlloc_7211_;
                        state = 51;
                        continue;
                    }
                }
            }
            51 => {
                return v___x_7210_;
            }
            52 => {
                if v_isShared_7216_ == 0 {
                    v___x_7218_ = v___x_7215_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_7219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7219_, 0, v_a_7213_);
                    v___x_7218_ = v_reuseFailAlloc_7219_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_7218_;
            }
            54 => {
                if v_isShared_7224_ == 0 {
                    v___x_7226_ = v___x_7223_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_7227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7227_, 0, v_a_7221_);
                    v___x_7226_ = v_reuseFailAlloc_7227_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_7226_;
            }
            56 => {
                if v_isShared_7232_ == 0 {
                    v___x_7234_ = v___x_7231_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_7235_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7235_, 0, v_a_7229_);
                    v___x_7234_ = v_reuseFailAlloc_7235_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_7234_;
            }
            58 => {
                if v_isShared_7240_ == 0 {
                    v___x_7242_ = v___x_7239_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_7243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7243_, 0, v_a_7237_);
                    v___x_7242_ = v_reuseFailAlloc_7243_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_7242_;
            }
            60 => {
                if v_isShared_7248_ == 0 {
                    v___x_7250_ = v___x_7247_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_7251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 0, v_a_7245_);
                    v___x_7250_ = v_reuseFailAlloc_7251_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_7250_;
            }
            62 => {
                if v_isShared_7258_ == 0 {
                    v___x_7260_ = v___x_7257_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_7261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7261_, 0, v_a_7255_);
                    v___x_7260_ = v_reuseFailAlloc_7261_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_7260_;
            }
            64 => {
                if v_isShared_7266_ == 0 {
                    v___x_7268_ = v___x_7265_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_7269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7269_, 0, v_a_7263_);
                    v___x_7268_ = v_reuseFailAlloc_7269_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_7268_;
            }
            66 => {
                if v_isShared_7274_ == 0 {
                    v___x_7276_ = v___x_7273_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_7277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7277_, 0, v_a_7271_);
                    v___x_7276_ = v_reuseFailAlloc_7277_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_7276_;
            }
            68 => {
                if v_isShared_7283_ == 0 {
                    v___x_7285_ = v___x_7282_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_7286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7286_, 0, v_a_7280_);
                    v___x_7285_ = v_reuseFailAlloc_7286_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_7285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_main___boxed(
    mut v_args_7289_: *mut leanh::LeanObject,
    mut v_a_7290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7291_ = _lean_main(v_args_7289_);
    return v_res_7291_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__1(
    mut v_as_7292_: *mut leanh::LeanObject,
    mut v_as_x27_7293_: *mut leanh::LeanObject,
    mut v_b_7294_: *mut leanh::LeanObject,
    mut v_a_7295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7297_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_7293_, v_b_7294_);
    return v___x_7297_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__1___boxed(
    mut v_as_7298_: *mut leanh::LeanObject,
    mut v_as_x27_7299_: *mut leanh::LeanObject,
    mut v_b_7300_: *mut leanh::LeanObject,
    mut v_a_7301_: *mut leanh::LeanObject,
    mut v___y_7302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7303_ = l_List_forIn_x27_loop___at___00main_spec__1(
        v_as_7298_,
        v_as_x27_7299_,
        v_b_7300_,
        v_a_7301_,
    );
    leanh::lean_dec(v_as_x27_7299_);
    leanh::lean_dec(v_as_7298_);
    return v_res_7303_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(
    mut v___y_7304_: *mut leanh::LeanObject,
    mut v___y_7305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7307_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_7305_);
    return v___x_7307_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(
    mut v___y_7308_: *mut leanh::LeanObject,
    mut v___y_7309_: *mut leanh::LeanObject,
    mut v___y_7310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7311_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_7308_, v___y_7309_);
    leanh::lean_dec(v___y_7309_);
    leanh::lean_dec_ref(v___y_7308_);
    return v_res_7311_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(
    mut v_00_u03b2_7312_: *mut leanh::LeanObject,
    mut v_m_7313_: *mut leanh::LeanObject,
    mut v_a_7314_: *mut leanh::LeanObject,
    mut v_fallback_7315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_7313_, v_a_7314_, v_fallback_7315_);
    return v___x_7316_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(
    mut v_00_u03b2_7317_: *mut leanh::LeanObject,
    mut v_m_7318_: *mut leanh::LeanObject,
    mut v_a_7319_: *mut leanh::LeanObject,
    mut v_fallback_7320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_7317_, v_m_7318_, v_a_7319_, v_fallback_7320_);
    leanh::lean_dec(v_fallback_7320_);
    leanh::lean_dec_ref(v_a_7319_);
    leanh::lean_dec_ref(v_m_7318_);
    return v_res_7321_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(
    mut v_00_u03b2_7322_: *mut leanh::LeanObject,
    mut v_m_7323_: *mut leanh::LeanObject,
    mut v_a_7324_: *mut leanh::LeanObject,
    mut v_b_7325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7326_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_7323_, v_a_7324_, v_b_7325_);
    return v___x_7326_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(
    mut v_n_7327_: *mut leanh::LeanObject,
    mut v_as_7328_: *mut leanh::LeanObject,
    mut v_lo_7329_: *mut leanh::LeanObject,
    mut v_hi_7330_: *mut leanh::LeanObject,
    mut v_w_7331_: *mut leanh::LeanObject,
    mut v_hlo_7332_: *mut leanh::LeanObject,
    mut v_hhi_7333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_7327_, v_as_7328_, v_lo_7329_, v_hi_7330_);
    return v___x_7334_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(
    mut v_n_7335_: *mut leanh::LeanObject,
    mut v_as_7336_: *mut leanh::LeanObject,
    mut v_lo_7337_: *mut leanh::LeanObject,
    mut v_hi_7338_: *mut leanh::LeanObject,
    mut v_w_7339_: *mut leanh::LeanObject,
    mut v_hlo_7340_: *mut leanh::LeanObject,
    mut v_hhi_7341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7342_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_7335_, v_as_7336_, v_lo_7337_, v_hi_7338_, v_w_7339_, v_hlo_7340_, v_hhi_7341_);
    leanh::lean_dec(v_hi_7338_);
    leanh::lean_dec(v_n_7335_);
    return v_res_7342_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(
    mut v_00_u03b2_7343_: *mut leanh::LeanObject,
    mut v_a_7344_: *mut leanh::LeanObject,
    mut v_fallback_7345_: *mut leanh::LeanObject,
    mut v_x_7346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7347_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_7344_, v_fallback_7345_, v_x_7346_);
    return v___x_7347_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(
    mut v_00_u03b2_7348_: *mut leanh::LeanObject,
    mut v_a_7349_: *mut leanh::LeanObject,
    mut v_fallback_7350_: *mut leanh::LeanObject,
    mut v_x_7351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7352_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_7348_, v_a_7349_, v_fallback_7350_, v_x_7351_);
    leanh::lean_dec(v_x_7351_);
    leanh::lean_dec(v_fallback_7350_);
    leanh::lean_dec_ref(v_a_7349_);
    return v_res_7352_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(
    mut v_00_u03b2_7353_: *mut leanh::LeanObject,
    mut v_a_7354_: *mut leanh::LeanObject,
    mut v_x_7355_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7356_: u8 = 0;
    v___x_7356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_7354_, v_x_7355_);
    return v___x_7356_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(
    mut v_00_u03b2_7357_: *mut leanh::LeanObject,
    mut v_a_7358_: *mut leanh::LeanObject,
    mut v_x_7359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7360_: u8 = 0;
    let mut v_r_7361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_7357_, v_a_7358_, v_x_7359_);
    leanh::lean_dec(v_x_7359_);
    leanh::lean_dec_ref(v_a_7358_);
    v_r_7361_ = leanh::lean_box((v_res_7360_) as usize);
    return v_r_7361_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(
    mut v_00_u03b2_7362_: *mut leanh::LeanObject,
    mut v_data_7363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_7363_);
    return v___x_7364_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(
    mut v_00_u03b2_7365_: *mut leanh::LeanObject,
    mut v_a_7366_: *mut leanh::LeanObject,
    mut v_b_7367_: *mut leanh::LeanObject,
    mut v_x_7368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_7366_, v_b_7367_, v_x_7368_);
    return v___x_7369_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(
    mut v_n_7370_: *mut leanh::LeanObject,
    mut v_lo_7371_: *mut leanh::LeanObject,
    mut v_hi_7372_: *mut leanh::LeanObject,
    mut v_hhi_7373_: *mut leanh::LeanObject,
    mut v_pivot_7374_: *mut leanh::LeanObject,
    mut v_as_7375_: *mut leanh::LeanObject,
    mut v_i_7376_: *mut leanh::LeanObject,
    mut v_k_7377_: *mut leanh::LeanObject,
    mut v_ilo_7378_: *mut leanh::LeanObject,
    mut v_ik_7379_: *mut leanh::LeanObject,
    mut v_w_7380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7381_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_7372_, v_pivot_7374_, v_as_7375_, v_i_7376_, v_k_7377_);
    return v___x_7381_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(
    mut v_n_7382_: *mut leanh::LeanObject,
    mut v_lo_7383_: *mut leanh::LeanObject,
    mut v_hi_7384_: *mut leanh::LeanObject,
    mut v_hhi_7385_: *mut leanh::LeanObject,
    mut v_pivot_7386_: *mut leanh::LeanObject,
    mut v_as_7387_: *mut leanh::LeanObject,
    mut v_i_7388_: *mut leanh::LeanObject,
    mut v_k_7389_: *mut leanh::LeanObject,
    mut v_ilo_7390_: *mut leanh::LeanObject,
    mut v_ik_7391_: *mut leanh::LeanObject,
    mut v_w_7392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_7382_, v_lo_7383_, v_hi_7384_, v_hhi_7385_, v_pivot_7386_, v_as_7387_, v_i_7388_, v_k_7389_, v_ilo_7390_, v_ik_7391_, v_w_7392_);
    leanh::lean_dec_ref(v_pivot_7386_);
    leanh::lean_dec(v_hi_7384_);
    leanh::lean_dec(v_lo_7383_);
    leanh::lean_dec(v_n_7382_);
    return v_res_7393_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(
    mut v_as_7394_: *mut leanh::LeanObject,
    mut v_sz_7395_: usize,
    mut v_i_7396_: usize,
    mut v_b_7397_: *mut leanh::LeanObject,
    mut v___y_7398_: *mut leanh::LeanObject,
    mut v___y_7399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_7394_, v_sz_7395_, v_i_7396_, v_b_7397_, v___y_7398_);
    return v___x_7401_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(
    mut v_as_7402_: *mut leanh::LeanObject,
    mut v_sz_7403_: *mut leanh::LeanObject,
    mut v_i_7404_: *mut leanh::LeanObject,
    mut v_b_7405_: *mut leanh::LeanObject,
    mut v___y_7406_: *mut leanh::LeanObject,
    mut v___y_7407_: *mut leanh::LeanObject,
    mut v___y_7408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7409_: usize = 0;
    let mut v_i_boxed_7410_: usize = 0;
    let mut v_res_7411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7409_ = leanh::lean_unbox_usize(v_sz_7403_);
    leanh::lean_dec(v_sz_7403_);
    v_i_boxed_7410_ = leanh::lean_unbox_usize(v_i_7404_);
    leanh::lean_dec(v_i_7404_);
    v_res_7411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_7402_, v_sz_boxed_7409_, v_i_boxed_7410_, v_b_7405_, v___y_7406_, v___y_7407_);
    leanh::lean_dec(v___y_7407_);
    leanh::lean_dec_ref(v___y_7406_);
    leanh::lean_dec_ref(v_as_7402_);
    return v_res_7411_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(
    mut v_00_u03b2_7412_: *mut leanh::LeanObject,
    mut v_i_7413_: *mut leanh::LeanObject,
    mut v_source_7414_: *mut leanh::LeanObject,
    mut v_target_7415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7416_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_7413_, v_source_7414_, v_target_7415_);
    return v___x_7416_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(
    mut v___x_7417_: u8,
    mut v_as_7418_: *mut leanh::LeanObject,
    mut v_sz_7419_: usize,
    mut v_i_7420_: usize,
    mut v_b_7421_: *mut leanh::LeanObject,
    mut v___y_7422_: *mut leanh::LeanObject,
    mut v___y_7423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_7417_, v_as_7418_, v_sz_7419_, v_i_7420_, v_b_7421_, v___y_7422_);
    return v___x_7425_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(
    mut v___x_7426_: *mut leanh::LeanObject,
    mut v_as_7427_: *mut leanh::LeanObject,
    mut v_sz_7428_: *mut leanh::LeanObject,
    mut v_i_7429_: *mut leanh::LeanObject,
    mut v_b_7430_: *mut leanh::LeanObject,
    mut v___y_7431_: *mut leanh::LeanObject,
    mut v___y_7432_: *mut leanh::LeanObject,
    mut v___y_7433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41215__boxed_7434_: u8 = 0;
    let mut v_sz_boxed_7435_: usize = 0;
    let mut v_i_boxed_7436_: usize = 0;
    let mut v_res_7437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41215__boxed_7434_ = (leanh::lean_unbox(v___x_7426_) as u8);
    v_sz_boxed_7435_ = leanh::lean_unbox_usize(v_sz_7428_);
    leanh::lean_dec(v_sz_7428_);
    v_i_boxed_7436_ = leanh::lean_unbox_usize(v_i_7429_);
    leanh::lean_dec(v_i_7429_);
    v_res_7437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41215__boxed_7434_, v_as_7427_, v_sz_boxed_7435_, v_i_boxed_7436_, v_b_7430_, v___y_7431_, v___y_7432_);
    leanh::lean_dec(v___y_7432_);
    leanh::lean_dec_ref(v___y_7431_);
    leanh::lean_dec_ref(v_as_7427_);
    return v_res_7437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(
    mut v_as_7438_: *mut leanh::LeanObject,
    mut v_sz_7439_: usize,
    mut v_i_7440_: usize,
    mut v_b_7441_: *mut leanh::LeanObject,
    mut v___y_7442_: *mut leanh::LeanObject,
    mut v___y_7443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_7438_, v_sz_7439_, v_i_7440_, v_b_7441_, v___y_7442_);
    return v___x_7445_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(
    mut v_as_7446_: *mut leanh::LeanObject,
    mut v_sz_7447_: *mut leanh::LeanObject,
    mut v_i_7448_: *mut leanh::LeanObject,
    mut v_b_7449_: *mut leanh::LeanObject,
    mut v___y_7450_: *mut leanh::LeanObject,
    mut v___y_7451_: *mut leanh::LeanObject,
    mut v___y_7452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7453_: usize = 0;
    let mut v_i_boxed_7454_: usize = 0;
    let mut v_res_7455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7453_ = leanh::lean_unbox_usize(v_sz_7447_);
    leanh::lean_dec(v_sz_7447_);
    v_i_boxed_7454_ = leanh::lean_unbox_usize(v_i_7448_);
    leanh::lean_dec(v_i_7448_);
    v_res_7455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_7446_, v_sz_boxed_7453_, v_i_boxed_7454_, v_b_7449_, v___y_7450_, v___y_7451_);
    leanh::lean_dec(v___y_7451_);
    leanh::lean_dec_ref(v___y_7450_);
    leanh::lean_dec_ref(v_as_7446_);
    return v_res_7455_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(
    mut v_00_u03b2_7456_: *mut leanh::LeanObject,
    mut v_x_7457_: *mut leanh::LeanObject,
    mut v_x_7458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7459_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_7457_, v_x_7458_);
    return v___x_7459_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(
    mut v___x_7460_: u8,
    mut v_as_7461_: *mut leanh::LeanObject,
    mut v_sz_7462_: usize,
    mut v_i_7463_: usize,
    mut v_b_7464_: *mut leanh::LeanObject,
    mut v___y_7465_: *mut leanh::LeanObject,
    mut v___y_7466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_7460_, v_as_7461_, v_sz_7462_, v_i_7463_, v_b_7464_, v___y_7465_);
    return v___x_7468_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(
    mut v___x_7469_: *mut leanh::LeanObject,
    mut v_as_7470_: *mut leanh::LeanObject,
    mut v_sz_7471_: *mut leanh::LeanObject,
    mut v_i_7472_: *mut leanh::LeanObject,
    mut v_b_7473_: *mut leanh::LeanObject,
    mut v___y_7474_: *mut leanh::LeanObject,
    mut v___y_7475_: *mut leanh::LeanObject,
    mut v___y_7476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41246__boxed_7477_: u8 = 0;
    let mut v_sz_boxed_7478_: usize = 0;
    let mut v_i_boxed_7479_: usize = 0;
    let mut v_res_7480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41246__boxed_7477_ = (leanh::lean_unbox(v___x_7469_) as u8);
    v_sz_boxed_7478_ = leanh::lean_unbox_usize(v_sz_7471_);
    leanh::lean_dec(v_sz_7471_);
    v_i_boxed_7479_ = leanh::lean_unbox_usize(v_i_7472_);
    leanh::lean_dec(v_i_7472_);
    v_res_7480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41246__boxed_7477_, v_as_7470_, v_sz_boxed_7478_, v_i_boxed_7479_, v_b_7473_, v___y_7474_, v___y_7475_);
    leanh::lean_dec(v___y_7475_);
    leanh::lean_dec_ref(v___y_7474_);
    leanh::lean_dec_ref(v_as_7470_);
    return v_res_7480_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_LeanIR(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Path(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_EmitRust(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Language_Lean(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_main___boxed__const__1 = _init_l_main___boxed__const__1();
    leanh::lean_mark_persistent(l_main___boxed__const__1);
    l_main___boxed__const__2 = _init_l_main___boxed__const__2();
    leanh::lean_mark_persistent(l_main___boxed__const__2);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_LeanIR(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_LeanIR(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Path(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_CSimpAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_EmitRust(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Language_Lean(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_LeanIR(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_LeanIR(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_LeanIR(builtin);
}
unsafe fn run_main(
    argc: core::ffi::c_int,
    argv: *mut *mut core::ffi::c_char,
) -> *mut leanh::LeanObject {
    let mut args_list = leanh::lean_box(0);
    let mut i = argc;
    while i > 1 {
        i -= 1;
        let arg_str = leanh::lean_mk_string(*argv.add(i as usize));
        let mut fields = [arg_str, args_list];
        args_list = leanh::lean_alloc_ctor(1, 2, 0);
        leanh::lean_ctor_set(args_list, 0, arg_str);
        leanh::lean_ctor_set(args_list, 1, fields[1]);
    }
    return _lean_main(args_list);
}
unsafe fn lean_rust_main(
    argc: core::ffi::c_int,
    mut argv: *mut *mut core::ffi::c_char,
) -> core::ffi::c_int {
    argv = leanh::lean_setup_args(argc, argv);
    leanh::lean_initialize();
    let res = runtime_initialize_LeanIR(1 /* builtin */);
    leanh::lean_io_mark_end_initialization();
    let mut ret_val = 1;
    if leanh::lean_io_result_is_ok(res) {
        leanh::lean_dec(res);
        leanh::lean_init_task_manager();
        let main_res = leanh::lean_run_main(run_main, argc, argv);
        leanh::lean_finalize_task_manager();
        if leanh::lean_io_result_is_ok(main_res) {
            ret_val =
                leanh::lean_unbox_uint32(leanh::lean_io_result_get_value(main_res))
                    as i32;
            leanh::lean_dec(main_res);
        } else {
            leanh::lean_io_result_show_error(main_res);
            leanh::lean_dec(main_res);
        }
    } else {
        leanh::lean_io_result_show_error(res);
        leanh::lean_dec(res);
    }
    return ret_val;
}

fn main() {
    let c_args: Vec<std::ffi::CString> = std::env::args()
        .map(|arg| std::ffi::CString::new(arg).expect("process argument contains NUL byte"))
        .collect();
    let mut raw_args: Vec<*mut core::ffi::c_char> = c_args
        .iter()
        .map(|arg| arg.as_ptr() as *mut core::ffi::c_char)
        .collect();
    let argc = raw_args.len() as core::ffi::c_int;
    let code = unsafe { lean_rust_main(argc, raw_args.as_mut_ptr()) };
    std::process::exit(code);
}
