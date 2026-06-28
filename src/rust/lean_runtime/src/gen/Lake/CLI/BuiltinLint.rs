// Lean compiler output
// Module: Lake.CLI.BuiltinLint
// Imports: Lean.Linter.EnvLinter Lean.Linter.PersistentLintLog Lean.CoreM Lake.Config.Workspace
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_getRoot;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_firstFrontendMacroScope,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lean::CoreM::{
    initialize_Lean_CoreM, l_Lean_Core_getMaxHeartbeats, l_Lean_diagnostics,
    runtime_initialize_Lean_CoreM,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isPrefixOf, l_Lean_Name_isSuffixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled, l_Lean_importModules,
    l_Lean_readModuleData,
};
use crate::r#gen::Lean::ImportingFlag::lean_enable_initializer_execution;
use crate::r#gen::Lean::Linter::EnvLinter::Frontend::{
    l_Lean_Linter_EnvLinter_formatLinterResults, l_Lean_Linter_EnvLinter_getChecks,
    l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg, l_Lean_Linter_EnvLinter_lintCore,
};
use crate::r#gen::Lean::Linter::EnvLinter::{
    initialize_Lean_Linter_EnvLinter, runtime_initialize_Lean_Linter_EnvLinter,
};
use crate::r#gen::Lean::Linter::PersistentLintLog::{
    initialize_Lean_Linter_PersistentLintLog, l_Lean_Linter_getAllLints,
    runtime_initialize_Lean_Linter_PersistentLintLog,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_toString, l_Lean_SerialMessage_toString,
};
use crate::r#gen::Lean::Util::LeanOptions::l_Lean_LeanOptions_ofArray;
use crate::r#gen::Lean::Util::Path::l_Lean_findOLean;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::l_Lean_inheritedTraceOptions;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_get_stderr, lean_get_stdout, lean_io_get_num_heartbeats,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::CompactedRegion::lean_compacted_region_free;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_box, lean_box_uint32,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [108, 105, 110, 116, 101, 114, 0],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [101, 120, 116, 114, 97, 0],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__1_value) as *mut LeanObject;
static l_Lake_BuiltinLint_leanOptOverrides___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__0_value)
                as *mut LeanObject,
            5701751079888345786 as *mut LeanObject,
        ],
    };
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__1_value)
                as *mut LeanObject,
            8383467597245298465 as *mut LeanObject,
        ],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__2_value) as *mut LeanObject;
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 1,
        },
        m_objs: [1 as *mut LeanObject],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__3_value) as *mut LeanObject;
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__4_value) as *mut LeanObject;
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__5_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [97, 108, 108, 0],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__5_value) as *mut LeanObject;
static l_Lake_BuiltinLint_leanOptOverrides___closed__6_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__0_value)
                as *mut LeanObject,
            5701751079888345786 as *mut LeanObject,
        ],
    };
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__5_value)
                as *mut LeanObject,
            12638910018443785458 as *mut LeanObject,
        ],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__6_value) as *mut LeanObject;
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__7_value) as *mut LeanObject;
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__8_value: LeanArrayObject<2> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__8_value) as *mut LeanObject;
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_BuiltinLint_leanOptOverrides___closed__10_value: LeanArrayObject<1> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [
            core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_leanOptOverrides___closed__10_value) as *mut LeanObject;
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_BuiltinLint_leanOptOverrides___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [45, 45, 32, 84, 101, 120, 116, 32, 108, 105, 110, 116, 101, 114, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 105, 110, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 35, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 110, 118, 76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2_value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3_value) as *mut LeanObject,5769806948869098747 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [45, 45, 32, 76, 105, 110, 116, 105, 110, 103, 32, 112, 97, 115, 115, 101, 100, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [45, 45, 32, 78, 111, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 32, 108, 105, 110, 116, 101, 114, 115, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 117, 110, 105, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16_value) as *mut LeanObject,3978731030111751661 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24_value) as *mut LeanObject;
pub static l_Lake_BuiltinLint_run___closed__0_value: LeanStringObject<52> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        108, 97, 107, 101, 32, 108, 105, 110, 116, 58, 32, 110, 111, 32, 109, 111, 100, 117, 108,
        101, 115, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 102, 111, 114, 32, 98, 117,
        105, 108, 116, 105, 110, 32, 108, 105, 110, 116, 105, 110, 103, 0,
    ],
};
static mut l_Lake_BuiltinLint_run___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuiltinLint_run___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuiltinLint_run___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_BuiltinLint_run___boxed__const__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lake_BuiltinLint_leanOptOverrides___closed__9() -> *mut LeanObject {
    let mut v_enableAll_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    v_enableAll_804_ = l_Lake_BuiltinLint_leanOptOverrides___closed__8;
    v___x_805_ = l_Lean_LeanOptions_ofArray(v_enableAll_804_);
    return v___x_805_;
}
pub unsafe fn _init_l_Lake_BuiltinLint_leanOptOverrides___closed__11() -> *mut LeanObject {
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Lake_BuiltinLint_leanOptOverrides___closed__10;
    v___x_811_ = l_Lean_LeanOptions_ofArray(v___x_810_);
    return v___x_811_;
}
pub unsafe fn l_Lake_BuiltinLint_leanOptOverrides(
    mut v_args_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_scope_813_: u8 = 0;
    let mut v_only_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: u8 = 0;
    v_scope_813_ = lean_ctor_get_uint8(
        v_args_812_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_only_814_ = lean_ctor_get(v_args_812_, 0);
    v___x_815_ = lean_array_get_size(v_only_814_);
    v___x_816_ = lean_unsigned_to_nat(0);
    v___x_817_ = lean_nat_dec_eq(v___x_815_, v___x_816_);
    if v___x_817_ == 0 {
        let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
        v___x_818_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_BuiltinLint_leanOptOverrides___closed__9),
            core::ptr::addr_of_mut!(l_Lake_BuiltinLint_leanOptOverrides___closed__9_once),
            _init_l_Lake_BuiltinLint_leanOptOverrides___closed__9,
        );
        return v___x_818_;
    } else {
        match v_scope_813_ {
            0 => {
                let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
                v___x_819_ = lean_box(1);
                return v___x_819_;
            }
            1 => {
                let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
                v___x_820_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_BuiltinLint_leanOptOverrides___closed__11),
                    core::ptr::addr_of_mut!(l_Lake_BuiltinLint_leanOptOverrides___closed__11_once),
                    _init_l_Lake_BuiltinLint_leanOptOverrides___closed__11,
                );
                return v___x_820_;
            }
            _ => {
                let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
                v___x_821_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_BuiltinLint_leanOptOverrides___closed__9),
                    core::ptr::addr_of_mut!(l_Lake_BuiltinLint_leanOptOverrides___closed__9_once),
                    _init_l_Lake_BuiltinLint_leanOptOverrides___closed__9,
                );
                return v___x_821_;
            }
        }
    }
}
pub unsafe fn l_Lake_BuiltinLint_leanOptOverrides___boxed(
    mut v_args_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_823_: *mut LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_822_);
    lean_dec_ref(v_args_822_);
    return v_res_823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(
    mut v___x_824_: *mut LeanObject,
    mut v_as_825_: *mut LeanObject,
    mut v_i_826_: usize,
    mut v_stop_827_: usize,
) -> u8 {
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: u8 = 0;
    let mut v___x_831_: usize = 0;
    let mut v___x_832_: usize = 0;
    let mut v___x_834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_828_ = lean_usize_dec_eq(v_i_826_, v_stop_827_);
                if v___x_828_ == 0 {
                    v___x_829_ = lean_array_uget_borrowed(v_as_825_, v_i_826_);
                    v___x_830_ = l_Lean_Name_isSuffixOf(v___x_829_, v___x_824_);
                    if v___x_830_ == 0 {
                        v___x_831_ = 1usize;
                        v___x_832_ = lean_usize_add(v_i_826_, v___x_831_);
                        v_i_826_ = v___x_832_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_830_;
                    }
                } else {
                    v___x_834_ = 0;
                    return v___x_834_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(
    mut v___x_835_: *mut LeanObject,
    mut v_as_836_: *mut LeanObject,
    mut v_i_837_: *mut LeanObject,
    mut v_stop_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_839_: usize = 0;
    let mut v_stop_boxed_840_: usize = 0;
    let mut v_res_841_: u8 = 0;
    let mut v_r_842_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_839_ = lean_unbox_usize(v_i_837_);
    lean_dec(v_i_837_);
    v_stop_boxed_840_ = lean_unbox_usize(v_stop_838_);
    lean_dec(v_stop_838_);
    v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v___x_835_, v_as_836_, v_i_boxed_839_, v_stop_boxed_840_);
    lean_dec_ref(v_as_836_);
    lean_dec(v___x_835_);
    v_r_842_ = lean_box((v_res_841_) as usize);
    return v_r_842_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(
    mut v_args_843_: *mut LeanObject,
    mut v_as_844_: *mut LeanObject,
    mut v_i_845_: usize,
    mut v_stop_846_: usize,
    mut v_b_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: usize = 0;
    let mut v___x_851_: usize = 0;
    let mut v___x_853_: u8 = 0;
    let mut v_scope_854_: u8 = 0;
    let mut v_only_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_858_: u8 = 0;
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linter_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: u8 = 0;
    let mut v___x_871_: u8 = 0;
    let mut v_linter_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: usize = 0;
    let mut v___x_874_: usize = 0;
    let mut v___x_875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_853_ = lean_usize_dec_eq(v_i_845_, v_stop_846_);
                if v___x_853_ == 0 {
                    v_scope_854_ = lean_ctor_get_uint8(
                        v_args_843_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_only_855_ = lean_ctor_get(v_args_843_, 0);
                    v___x_856_ = lean_array_uget_borrowed(v_as_844_, v_i_845_);
                    v___x_868_ = lean_array_get_size(v_only_855_);
                    v___x_869_ = lean_unsigned_to_nat(0);
                    v___x_870_ = lean_nat_dec_eq(v___x_868_, v___x_869_);
                    if v___x_870_ == 0 {
                        v___x_871_ = lean_nat_dec_lt(v___x_869_, v___x_868_);
                        if v___x_871_ == 0 {
                            v___y_858_ = v___x_870_;
                            state = 2;
                            continue;
                        } else {
                            if v___x_871_ == 0 {
                                v___y_858_ = v___x_870_;
                                state = 2;
                                continue;
                            } else {
                                v_linter_872_ = lean_ctor_get(v___x_856_, 0);
                                v___x_873_ = 0usize;
                                v___x_874_ = lean_usize_of_nat(v___x_868_);
                                v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_linter_872_, v_only_855_, v___x_873_, v___x_874_);
                                v___y_858_ = v___x_875_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___y_858_ = v___x_870_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_b_847_;
                }
            }
            1 => {
                v___x_850_ = 1usize;
                v___x_851_ = lean_usize_add(v_i_845_, v___x_850_);
                v_i_845_ = v___x_851_;
                v_b_847_ = v___y_849_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_858_ == 0 {
                    v___y_849_ = v_b_847_;
                    state = 1;
                    continue;
                } else {
                    v___x_859_ = lean_array_get_size(v_only_855_);
                    v___x_860_ = lean_unsigned_to_nat(0);
                    v___x_861_ = lean_nat_dec_eq(v___x_859_, v___x_860_);
                    if v___x_861_ == 0 {
                        lean_inc(v___x_856_);
                        v___x_862_ = lean_array_push(v_b_847_, v___x_856_);
                        v___y_849_ = v___x_862_;
                        state = 1;
                        continue;
                    } else {
                        if v_scope_854_ == 0 {
                            v_linter_863_ = lean_ctor_get(v___x_856_, 0);
                            v___x_864_ = l_Lake_BuiltinLint_leanOptOverrides___closed__2;
                            v___x_865_ = l_Lean_Name_isPrefixOf(v___x_864_, v_linter_863_);
                            if v___x_865_ == 0 {
                                lean_inc(v___x_856_);
                                v___x_866_ = lean_array_push(v_b_847_, v___x_856_);
                                v___y_849_ = v___x_866_;
                                state = 1;
                                continue;
                            } else {
                                v___y_849_ = v_b_847_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_inc(v___x_856_);
                            v___x_867_ = lean_array_push(v_b_847_, v___x_856_);
                            v___y_849_ = v___x_867_;
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
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1___boxed(
    mut v_args_876_: *mut LeanObject,
    mut v_as_877_: *mut LeanObject,
    mut v_i_878_: *mut LeanObject,
    mut v_stop_879_: *mut LeanObject,
    mut v_b_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_881_: usize = 0;
    let mut v_stop_boxed_882_: usize = 0;
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_881_ = lean_unbox_usize(v_i_878_);
    lean_dec(v_i_878_);
    v_stop_boxed_882_ = lean_unbox_usize(v_stop_879_);
    lean_dec(v_stop_879_);
    v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_876_, v_as_877_, v_i_boxed_881_, v_stop_boxed_882_, v_b_880_);
    lean_dec_ref(v_as_877_);
    lean_dec_ref(v_args_876_);
    return v_res_883_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(
    mut v_pkgRoot_886_: *mut LeanObject,
    mut v_args_887_: *mut LeanObject,
    mut v_as_888_: *mut LeanObject,
    mut v_i_889_: usize,
    mut v_stop_890_: usize,
    mut v_b_891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: usize = 0;
    let mut v___x_895_: usize = 0;
    let mut v___x_897_: u8 = 0;
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___y_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: u8 = 0;
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_918_: u8 = 0;
    let mut v___x_919_: usize = 0;
    let mut v___x_920_: usize = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: usize = 0;
    let mut v___x_923_: usize = 0;
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_897_ = lean_usize_dec_eq(v_i_889_, v_stop_890_);
                if v___x_897_ == 0 {
                    v___x_898_ = lean_array_uget(v_as_888_, v_i_889_);
                    v_fst_899_ = lean_ctor_get(v___x_898_, 0);
                    v_snd_900_ = lean_ctor_get(v___x_898_, 1);
                    v_isSharedCheck_925_ = (!lean_is_exclusive(v___x_898_)) as u8;
                    if v_isSharedCheck_925_ == 0 {
                        v___x_902_ = v___x_898_;
                        v_isShared_903_ = v_isSharedCheck_925_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_900_);
                        lean_inc(v_fst_899_);
                        lean_dec(v___x_898_);
                        v___x_902_ = lean_box(0);
                        v_isShared_903_ = v_isSharedCheck_925_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_b_891_;
                }
            }
            1 => {
                v___x_894_ = 1usize;
                v___x_895_ = lean_usize_add(v_i_889_, v___x_894_);
                v_i_889_ = v___x_895_;
                v_b_891_ = v___y_893_;
                state = 0;
                continue;
            }
            2 => {
                v___x_913_ = l_Lean_Name_isPrefixOf(v_pkgRoot_886_, v_fst_899_);
                if v___x_913_ == 0 {
                    lean_del_object(v___x_902_);
                    lean_dec(v_snd_900_);
                    lean_dec(v_fst_899_);
                    v___y_893_ = v_b_891_;
                    state = 1;
                    continue;
                } else {
                    v___x_914_ = lean_unsigned_to_nat(0);
                    v___x_915_ = lean_array_get_size(v_snd_900_);
                    v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0;
                    v___x_917_ = lean_nat_dec_lt(v___x_914_, v___x_915_);
                    if v___x_917_ == 0 {
                        lean_dec(v_snd_900_);
                        v___y_905_ = v___x_916_;
                        state = 3;
                        continue;
                    } else {
                        v___x_918_ = lean_nat_dec_le(v___x_915_, v___x_915_);
                        if v___x_918_ == 0 {
                            if v___x_917_ == 0 {
                                lean_dec(v_snd_900_);
                                v___y_905_ = v___x_916_;
                                state = 3;
                                continue;
                            } else {
                                v___x_919_ = 0usize;
                                v___x_920_ = lean_usize_of_nat(v___x_915_);
                                v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_887_, v_snd_900_, v___x_919_, v___x_920_, v___x_916_);
                                lean_dec(v_snd_900_);
                                v___y_905_ = v___x_921_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_922_ = 0usize;
                            v___x_923_ = lean_usize_of_nat(v___x_915_);
                            v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_887_, v_snd_900_, v___x_922_, v___x_923_, v___x_916_);
                            lean_dec(v_snd_900_);
                            v___y_905_ = v___x_924_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_906_ = lean_array_get_size(v___y_905_);
                v___x_907_ = lean_unsigned_to_nat(0);
                v___x_908_ = lean_nat_dec_eq(v___x_906_, v___x_907_);
                if v___x_908_ == 0 {
                    if v_isShared_903_ == 0 {
                        lean_ctor_set(v___x_902_, 1, v___y_905_);
                        v___x_910_ = v___x_902_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_912_, 0, v_fst_899_);
                        lean_ctor_set(v_reuseFailAlloc_912_, 1, v___y_905_);
                        v___x_910_ = v_reuseFailAlloc_912_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_905_);
                    lean_del_object(v___x_902_);
                    lean_dec(v_fst_899_);
                    v___y_893_ = v_b_891_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_911_ = lean_array_push(v_b_891_, v___x_910_);
                v___y_893_ = v___x_911_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___boxed(
    mut v_pkgRoot_926_: *mut LeanObject,
    mut v_args_927_: *mut LeanObject,
    mut v_as_928_: *mut LeanObject,
    mut v_i_929_: *mut LeanObject,
    mut v_stop_930_: *mut LeanObject,
    mut v_b_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_932_: usize = 0;
    let mut v_stop_boxed_933_: usize = 0;
    let mut v_res_934_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_932_ = lean_unbox_usize(v_i_929_);
    lean_dec(v_i_929_);
    v_stop_boxed_933_ = lean_unbox_usize(v_stop_930_);
    lean_dec(v_stop_930_);
    v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_926_, v_args_927_, v_as_928_, v_i_boxed_932_, v_stop_boxed_933_, v_b_931_);
    lean_dec_ref(v_as_928_);
    lean_dec_ref(v_args_927_);
    lean_dec(v_pkgRoot_926_);
    return v_res_934_;
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(
    mut v_env_937_: *mut LeanObject,
    mut v_args_938_: *mut LeanObject,
    mut v_pkgRoot_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: u8 = 0;
    v___x_940_ = lean_unsigned_to_nat(0);
    v___x_941_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0;
    v___x_942_ = l_Lean_Linter_getAllLints(v_env_937_);
    v___x_943_ = lean_array_get_size(v___x_942_);
    v___x_944_ = lean_nat_dec_lt(v___x_940_, v___x_943_);
    if v___x_944_ == 0 {
        lean_dec_ref(v___x_942_);
        return v___x_941_;
    } else {
        let mut v___x_945_: u8 = 0;
        v___x_945_ = lean_nat_dec_le(v___x_943_, v___x_943_);
        if v___x_945_ == 0 {
            if v___x_944_ == 0 {
                lean_dec_ref(v___x_942_);
                return v___x_941_;
            } else {
                let mut v___x_946_: usize = 0;
                let mut v___x_947_: usize = 0;
                let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
                v___x_946_ = 0usize;
                v___x_947_ = lean_usize_of_nat(v___x_943_);
                v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_939_, v_args_938_, v___x_942_, v___x_946_, v___x_947_, v___x_941_);
                lean_dec_ref(v___x_942_);
                return v___x_948_;
            }
        } else {
            let mut v___x_949_: usize = 0;
            let mut v___x_950_: usize = 0;
            let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
            v___x_949_ = 0usize;
            v___x_950_ = lean_usize_of_nat(v___x_943_);
            v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_939_, v_args_938_, v___x_942_, v___x_949_, v___x_950_, v___x_941_);
            lean_dec_ref(v___x_942_);
            return v___x_951_;
        }
    }
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(
    mut v_env_952_: *mut LeanObject,
    mut v_args_953_: *mut LeanObject,
    mut v_pkgRoot_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_955_: *mut LeanObject = core::ptr::null_mut();
    v_res_955_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(
        v_env_952_,
        v_args_953_,
        v_pkgRoot_954_,
    );
    lean_dec(v_pkgRoot_954_);
    lean_dec_ref(v_args_953_);
    lean_dec_ref(v_env_952_);
    return v_res_955_;
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(
    mut v_modData_956_: *mut LeanObject,
) -> u8 {
    let mut v_isModule_958_: u8 = 0;
    v_isModule_958_ = lean_ctor_get_uint8(
        v_modData_956_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
    );
    return v_isModule_958_;
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(
    mut v_modData_959_: *mut LeanObject,
    mut v_a_960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_961_: u8 = 0;
    let mut v_r_962_: *mut LeanObject = core::ptr::null_mut();
    v_res_961_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_959_);
    lean_dec_ref(v_modData_959_);
    v_r_962_ = lean_box((v_res_961_) as usize);
    return v_r_962_;
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1() -> *mut LeanObject
{
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    v___x_964_ = lean_enable_initializer_execution();
    return v___x_964_;
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(
    mut v_a_965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_966_: *mut LeanObject = core::ptr::null_mut();
    v_res_966_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
    return v_res_966_;
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(
    mut v_region_967_: usize,
) -> *mut LeanObject {
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    v___x_969_ = lean_compacted_region_free(v_region_967_);
    return v___x_969_;
}
pub unsafe fn l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(
    mut v_region_970_: *mut LeanObject,
    mut v_a_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_region_boxed_972_: usize = 0;
    let mut v_res_973_: *mut LeanObject = core::ptr::null_mut();
    v_region_boxed_972_ = lean_unbox_usize(v_region_970_);
    lean_dec(v_region_970_);
    v_res_973_ =
        l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_boxed_972_);
    return v_res_973_;
}
pub unsafe fn l_IO_print___at___00Lake_BuiltinLint_run_spec__0(
    mut v_s_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = lean_get_stdout();
    v_putStr_977_ = lean_ctor_get(v___x_976_, 4);
    lean_inc_ref(v_putStr_977_);
    lean_dec_ref(v___x_976_);
    v___x_978_ = lean_apply_2(v_putStr_977_, v_s_974_, lean_box(0));
    return v___x_978_;
}
pub unsafe fn l_IO_print___at___00Lake_BuiltinLint_run_spec__0___boxed(
    mut v_s_979_: *mut LeanObject,
    mut v_a_980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_981_: *mut LeanObject = core::ptr::null_mut();
    v_res_981_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v_s_979_);
    return v_res_981_;
}
pub unsafe fn l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4(
    mut v_opts_982_: *mut LeanObject,
    mut v_opt_983_: *mut LeanObject,
) -> u8 {
    let mut v_name_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v_name_984_ = lean_ctor_get(v_opt_983_, 0);
    v_defValue_985_ = lean_ctor_get(v_opt_983_, 1);
    v_map_986_ = lean_ctor_get(v_opts_982_, 0);
    v___x_987_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_986_,
            v_name_984_,
        );
    if lean_obj_tag(v___x_987_) == 0 {
        let mut v___x_988_: u8 = 0;
        v___x_988_ = (lean_unbox(v_defValue_985_) as u8);
        return v___x_988_;
    } else {
        let mut v_val_989_: *mut LeanObject = core::ptr::null_mut();
        v_val_989_ = lean_ctor_get(v___x_987_, 0);
        lean_inc(v_val_989_);
        lean_dec_ref_known(v___x_987_, 1);
        if lean_obj_tag(v_val_989_) == 1 {
            let mut v_v_990_: u8 = 0;
            v_v_990_ = lean_ctor_get_uint8(v_val_989_, 0 as u32);
            lean_dec_ref_known(v_val_989_, 0);
            return v_v_990_;
        } else {
            let mut v___x_991_: u8 = 0;
            lean_dec(v_val_989_);
            v___x_991_ = (lean_unbox(v_defValue_985_) as u8);
            return v___x_991_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4___boxed(
    mut v_opts_992_: *mut LeanObject,
    mut v_opt_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_994_: u8 = 0;
    let mut v_r_995_: *mut LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4(v_opts_992_, v_opt_993_);
    lean_dec_ref(v_opt_993_);
    lean_dec_ref(v_opts_992_);
    v_r_995_ = lean_box((v_res_994_) as usize);
    return v_r_995_;
}
pub unsafe fn l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5(
    mut v_opts_996_: *mut LeanObject,
    mut v_opt_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    v_name_998_ = lean_ctor_get(v_opt_997_, 0);
    v_defValue_999_ = lean_ctor_get(v_opt_997_, 1);
    v_map_1000_ = lean_ctor_get(v_opts_996_, 0);
    v___x_1001_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1000_,
            v_name_998_,
        );
    if lean_obj_tag(v___x_1001_) == 0 {
        lean_inc(v_defValue_999_);
        return v_defValue_999_;
    } else {
        let mut v_val_1002_: *mut LeanObject = core::ptr::null_mut();
        v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
        lean_inc(v_val_1002_);
        lean_dec_ref_known(v___x_1001_, 1);
        if lean_obj_tag(v_val_1002_) == 3 {
            let mut v_v_1003_: *mut LeanObject = core::ptr::null_mut();
            v_v_1003_ = lean_ctor_get(v_val_1002_, 0);
            lean_inc(v_v_1003_);
            lean_dec_ref_known(v_val_1002_, 1);
            return v_v_1003_;
        } else {
            lean_dec(v_val_1002_);
            lean_inc(v_defValue_999_);
            return v_defValue_999_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5___boxed(
    mut v_opts_1004_: *mut LeanObject,
    mut v_opt_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1006_: *mut LeanObject = core::ptr::null_mut();
    v_res_1006_ =
        l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5(v_opts_1004_, v_opt_1005_);
    lean_dec_ref(v_opt_1005_);
    lean_dec_ref(v_opts_1004_);
    return v_res_1006_;
}
pub unsafe fn l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8(
    mut v_s_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = lean_get_stderr();
    v_putStr_1010_ = lean_ctor_get(v___x_1009_, 4);
    lean_inc_ref(v_putStr_1010_);
    lean_dec_ref(v___x_1009_);
    v___x_1011_ = lean_apply_2(v_putStr_1010_, v_s_1007_, lean_box(0));
    return v___x_1011_;
}
pub unsafe fn l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8___boxed(
    mut v_s_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1014_: *mut LeanObject = core::ptr::null_mut();
    v_res_1014_ =
        l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8(v_s_1012_);
    return v_res_1014_;
}
pub unsafe fn l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8(
    mut v_s_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1017_: u32 = 0;
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = 10;
    v___x_1018_ = lean_string_push(v_s_1015_, v___x_1017_);
    v___x_1019_ =
        l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8(v___x_1018_);
    return v___x_1019_;
}
pub unsafe fn l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8___boxed(
    mut v_s_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1022_: *mut LeanObject = core::ptr::null_mut();
    v_res_1022_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8(v_s_1020_);
    return v_res_1022_;
}
pub unsafe fn l_IO_println___at___00Lake_BuiltinLint_run_spec__1(
    mut v_s_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1025_: u32 = 0;
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v___x_1025_ = 10;
    v___x_1026_ = lean_string_push(v_s_1023_, v___x_1025_);
    v___x_1027_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v___x_1026_);
    return v___x_1027_;
}
pub unsafe fn l_IO_println___at___00Lake_BuiltinLint_run_spec__1___boxed(
    mut v_s_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v_s_1028_);
    return v_res_1030_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(
    mut v___x_1031_: *mut LeanObject,
    mut v_as_1032_: *mut LeanObject,
    mut v_sz_1033_: usize,
    mut v_i_1034_: usize,
    mut v_b_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_message_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anyFailed_1042_: u8 = 0;
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: usize = 0;
    let mut v___x_1047_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1037_ = lean_usize_dec_lt(v_i_1034_, v_sz_1033_);
                if v___x_1037_ == 0 {
                    v___x_1038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1038_, 0, v_b_1035_);
                    return v___x_1038_;
                } else {
                    v_a_1039_ = lean_array_uget_borrowed(v_as_1032_, v_i_1034_);
                    v_message_1040_ = lean_ctor_get(v_a_1039_, 1);
                    v___x_1041_ = lean_unsigned_to_nat(0);
                    v_anyFailed_1042_ = lean_nat_dec_eq(v___x_1031_, v___x_1041_);
                    lean_inc_ref(v_message_1040_);
                    v___x_1043_ = l_Lean_SerialMessage_toString(v_message_1040_, v_anyFailed_1042_);
                    v___x_1044_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v___x_1043_);
                    if lean_obj_tag(v___x_1044_) == 0 {
                        lean_dec_ref_known(v___x_1044_, 1);
                        v___x_1045_ = lean_box(0);
                        v___x_1046_ = 1usize;
                        v___x_1047_ = lean_usize_add(v_i_1034_, v___x_1046_);
                        v_i_1034_ = v___x_1047_;
                        v_b_1035_ = v___x_1045_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1044_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___boxed(
    mut v___x_1049_: *mut LeanObject,
    mut v_as_1050_: *mut LeanObject,
    mut v_sz_1051_: *mut LeanObject,
    mut v_i_1052_: *mut LeanObject,
    mut v_b_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1055_: usize = 0;
    let mut v_i_boxed_1056_: usize = 0;
    let mut v_res_1057_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1051_);
    lean_dec(v_sz_1051_);
    v_i_boxed_1056_ = lean_unbox_usize(v_i_1052_);
    lean_dec(v_i_1052_);
    v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_1049_, v_as_1050_, v_sz_boxed_1055_, v_i_boxed_1056_, v_b_1053_);
    lean_dec_ref(v_as_1050_);
    lean_dec(v___x_1049_);
    return v_res_1057_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(
    mut v___x_1060_: *mut LeanObject,
    mut v_as_1061_: *mut LeanObject,
    mut v_sz_1062_: usize,
    mut v_i_1063_: usize,
    mut v_b_1064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1078_: usize = 0;
    let mut v___x_1079_: usize = 0;
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1066_ = lean_usize_dec_lt(v_i_1063_, v_sz_1062_);
                if v___x_1066_ == 0 {
                    v___x_1067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1067_, 0, v_b_1064_);
                    return v___x_1067_;
                } else {
                    v_a_1068_ = lean_array_uget_borrowed(v_as_1061_, v_i_1063_);
                    v_fst_1069_ = lean_ctor_get(v_a_1068_, 0);
                    v_snd_1070_ = lean_ctor_get(v_a_1068_, 1);
                    v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0;
                    lean_inc(v_fst_1069_);
                    v___x_1072_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_fst_1069_,
                        v___x_1066_,
                    );
                    v___x_1073_ = lean_string_append(v___x_1071_, v___x_1072_);
                    lean_dec_ref(v___x_1072_);
                    v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1;
                    v___x_1075_ = lean_string_append(v___x_1073_, v___x_1074_);
                    v___x_1076_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v___x_1075_);
                    if lean_obj_tag(v___x_1076_) == 0 {
                        lean_dec_ref_known(v___x_1076_, 1);
                        v___x_1077_ = lean_box(0);
                        v_sz_1078_ = lean_array_size(v_snd_1070_);
                        v___x_1079_ = 0usize;
                        v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_1060_, v_snd_1070_, v_sz_1078_, v___x_1079_, v___x_1077_);
                        if lean_obj_tag(v___x_1080_) == 0 {
                            lean_dec_ref_known(v___x_1080_, 1);
                            v___x_1081_ = 1usize;
                            v___x_1082_ = lean_usize_add(v_i_1063_, v___x_1081_);
                            v_i_1063_ = v___x_1082_;
                            v_b_1064_ = v___x_1077_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1080_;
                        }
                    } else {
                        return v___x_1076_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(
    mut v___x_1084_: *mut LeanObject,
    mut v_as_1085_: *mut LeanObject,
    mut v_sz_1086_: *mut LeanObject,
    mut v_i_1087_: *mut LeanObject,
    mut v_b_1088_: *mut LeanObject,
    mut v___y_1089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1090_: usize = 0;
    let mut v_i_boxed_1091_: usize = 0;
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1090_ = lean_unbox_usize(v_sz_1086_);
    lean_dec(v_sz_1086_);
    v_i_boxed_1091_ = lean_unbox_usize(v_i_1087_);
    lean_dec(v_i_1087_);
    v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_1084_, v_as_1085_, v_sz_boxed_1090_, v_i_boxed_1091_, v_b_1088_);
    lean_dec_ref(v_as_1085_);
    lean_dec(v___x_1084_);
    return v_res_1092_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6(
    mut v___x_1093_: *mut LeanObject,
    mut v_as_1094_: *mut LeanObject,
    mut v_i_1095_: usize,
    mut v_stop_1096_: usize,
) -> u8 {
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    let mut v___x_1103_: u8 = 0;
    let mut v___x_1104_: u8 = 0;
    let mut v___x_1105_: usize = 0;
    let mut v___x_1106_: usize = 0;
    let mut v___x_1108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1097_ = lean_usize_dec_eq(v_i_1095_, v_stop_1096_);
                if v___x_1097_ == 0 {
                    v___x_1098_ = lean_array_uget_borrowed(v_as_1094_, v_i_1095_);
                    v_snd_1099_ = lean_ctor_get(v___x_1098_, 1);
                    v_size_1100_ = lean_ctor_get(v_snd_1099_, 0);
                    v___x_1101_ = lean_unsigned_to_nat(0);
                    v___x_1102_ = 1;
                    v___x_1103_ = lean_nat_dec_eq(v_size_1100_, v___x_1101_);
                    if v___x_1103_ == 0 {
                        return v___x_1102_;
                    } else {
                        v___x_1104_ = lean_nat_dec_eq(v___x_1093_, v___x_1101_);
                        if v___x_1104_ == 0 {
                            v___x_1105_ = 1usize;
                            v___x_1106_ = lean_usize_add(v_i_1095_, v___x_1105_);
                            v_i_1095_ = v___x_1106_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1102_;
                        }
                    }
                } else {
                    v___x_1108_ = 0;
                    return v___x_1108_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6___boxed(
    mut v___x_1109_: *mut LeanObject,
    mut v_as_1110_: *mut LeanObject,
    mut v_i_1111_: *mut LeanObject,
    mut v_stop_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1113_: usize = 0;
    let mut v_stop_boxed_1114_: usize = 0;
    let mut v_res_1115_: u8 = 0;
    let mut v_r_1116_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1113_ = lean_unbox_usize(v_i_1111_);
    lean_dec(v_i_1111_);
    v_stop_boxed_1114_ = lean_unbox_usize(v_stop_1112_);
    lean_dec(v_stop_1112_);
    v_res_1115_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6(v___x_1109_, v_as_1110_, v_i_boxed_1113_, v_stop_boxed_1114_);
    lean_dec_ref(v_as_1110_);
    lean_dec(v___x_1109_);
    v_r_1116_ = lean_box((v_res_1115_) as usize);
    return v_r_1116_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9()
-> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = lean_unsigned_to_nat(32);
    v___x_1130_ = lean_mk_empty_array_with_capacity(v___x_1129_);
    v___x_1131_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    return v___x_1131_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10()
-> *mut LeanObject {
    let mut v___x_1132_: usize = 0;
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = 5usize;
    v___x_1133_ = lean_unsigned_to_nat(0);
    v___x_1134_ = lean_unsigned_to_nat(32);
    v___x_1135_ = lean_mk_empty_array_with_capacity(v___x_1134_);
    v___x_1136_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9);
    v___x_1137_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    lean_ctor_set(v___x_1137_, 1, v___x_1135_);
    lean_ctor_set(v___x_1137_, 2, v___x_1133_);
    lean_ctor_set(v___x_1137_, 3, v___x_1133_);
    lean_ctor_set_usize(v___x_1137_, 4, v___x_1132_);
    return v___x_1137_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11()
-> *mut LeanObject {
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    v___x_1138_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1138_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12()
-> *mut LeanObject {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    v___x_1139_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11);
    v___x_1140_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1140_, 0, v___x_1139_);
    return v___x_1140_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13()
-> *mut LeanObject {
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    v___x_1141_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12);
    v___x_1142_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1142_, 0, v___x_1141_);
    lean_ctor_set(v___x_1142_, 1, v___x_1141_);
    return v___x_1142_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14()
-> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = l_Lean_NameSet_empty;
    v___x_1144_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10);
    v___x_1145_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1145_, 0, v___x_1144_);
    lean_ctor_set(v___x_1145_, 1, v___x_1144_);
    lean_ctor_set(v___x_1145_, 2, v___x_1143_);
    return v___x_1145_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15()
-> *mut LeanObject {
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    v___x_1146_ = lean_unsigned_to_nat(1);
    v___x_1147_ = l_Lean_firstFrontendMacroScope;
    v___x_1148_ = lean_nat_add(v___x_1147_, v___x_1146_);
    return v___x_1148_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20()
-> *mut LeanObject {
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u64 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1159_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10);
    v___x_1160_ = 0u64;
    v___x_1161_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_1161_, 0, v___x_1159_);
    lean_ctor_set_uint64(
        v___x_1161_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1160_,
    );
    return v___x_1161_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21()
-> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anyFailed_1164_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10);
    v___x_1163_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12);
    v_anyFailed_1164_ = 1;
    v___x_1165_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_1165_, 0, v___x_1163_);
    lean_ctor_set(v___x_1165_, 1, v___x_1163_);
    lean_ctor_set(v___x_1165_, 2, v___x_1162_);
    lean_ctor_set_uint8(
        v___x_1165_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_anyFailed_1164_,
    );
    return v___x_1165_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7(
    mut v___x_1171_: *mut LeanObject,
    mut v_args_1172_: *mut LeanObject,
    mut v_scope_1173_: u8,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: u8,
    mut v_as_1176_: *mut LeanObject,
    mut v_sz_1177_: usize,
    mut v_i_1178_: usize,
    mut v_b_1179_: u8,
) -> *mut LeanObject {
    let mut v_a_1182_: u8 = 0;
    let mut v___x_1183_: usize = 0;
    let mut v___x_1184_: usize = 0;
    let mut v_msg_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anyFailed_1201_: u8 = 0;
    let mut v_anyFailed_1202_: u8 = 0;
    let mut v___y_1204_: u8 = 0;
    let mut v___y_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1206_: u8 = 0;
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1211_: u8 = 0;
    let mut v___y_1212_: u8 = 0;
    let mut v___y_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1218_: u8 = 0;
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut v_a_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_envLinterModule_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: u8 = 0;
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1245_: u8 = 0;
    let mut v___y_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1250_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1266_: u8 = 0;
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v___y_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1273_: u8 = 0;
    let mut v___y_1274_: usize = 0;
    let mut v___y_1275_: u8 = 0;
    let mut v___y_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1291_: u8 = 0;
    let mut v_inheritedTraceOptions_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1295_: u8 = 0;
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: u8 = 0;
    let mut v_a_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1322_: u8 = 0;
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut v_a_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut v_unused_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: u8 = 0;
    let mut v___y_1340_: usize = 0;
    let mut v___y_1341_: u8 = 0;
    let mut v___y_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1344_: u8 = 0;
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut v_unused_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1369_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1371_: usize = 0;
    let mut v___x_1372_: usize = 0;
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: u8 = 0;
    let mut v_a_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1409_: u8 = 0;
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: u8 = 0;
    let mut v___y_1418_: u8 = 0;
    let mut v___x_1419_: usize = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u32 = 0;
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v_a_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1451_: u8 = 0;
    let mut v___x_1452_: u8 = 0;
    let mut v___x_1453_: u8 = 0;
    let mut v_a_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1457_: u8 = 0;
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_a_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut v_a_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1200_ = lean_unsigned_to_nat(0);
                v_anyFailed_1201_ = lean_nat_dec_eq(v___x_1171_, v___x_1200_);
                v_anyFailed_1202_ = 1;
                v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4;
                v_envLinterModule_1236_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v_envLinterModule_1236_, 0, v___x_1235_);
                lean_ctor_set_uint8(
                    v_envLinterModule_1236_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_anyFailed_1201_,
                );
                lean_ctor_set_uint8(
                    v_envLinterModule_1236_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_anyFailed_1202_,
                );
                lean_ctor_set_uint8(
                    v_envLinterModule_1236_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v_anyFailed_1201_,
                );
                v___x_1237_ = lean_usize_dec_lt(v_i_1178_, v_sz_1177_);
                if v___x_1237_ == 0 {
                    lean_dec_ref_known(v_envLinterModule_1236_, 1);
                    v___x_1238_ = lean_box((v_b_1179_) as usize);
                    v___x_1239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1239_, 0, v___x_1238_);
                    return v___x_1239_;
                } else {
                    v___x_1240_ = lean_enable_initializer_execution();
                    if lean_obj_tag(v___x_1240_) == 0 {
                        lean_dec_ref_known(v___x_1240_, 1);
                        v_a_1241_ = lean_array_uget_borrowed(v_as_1176_, v_i_1178_);
                        lean_inc(v_a_1241_);
                        v___x_1410_ = l_Lean_findOLean(v_a_1241_);
                        if lean_obj_tag(v___x_1410_) == 0 {
                            v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
                            lean_inc(v_a_1411_);
                            lean_dec_ref_known(v___x_1410_, 1);
                            v___x_1412_ = l_Lean_readModuleData(v_a_1411_);
                            lean_dec(v_a_1411_);
                            if lean_obj_tag(v___x_1412_) == 0 {
                                v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
                                lean_inc(v_a_1413_);
                                lean_dec_ref_known(v___x_1412_, 1);
                                v_fst_1414_ = lean_ctor_get(v_a_1413_, 0);
                                lean_inc(v_fst_1414_);
                                v_snd_1415_ = lean_ctor_get(v_a_1413_, 1);
                                lean_inc(v_snd_1415_);
                                lean_dec(v_a_1413_);
                                v___x_1416_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_1414_);
                                lean_dec(v_fst_1414_);
                                if v___x_1416_ == 0 {
                                    v___x_1452_ = 2;
                                    v___y_1418_ = v___x_1452_;
                                    state = 22;
                                    continue;
                                } else {
                                    v___x_1453_ = 0;
                                    v___y_1418_ = v___x_1453_;
                                    state = 22;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_envLinterModule_1236_, 1);
                                v_a_1454_ = lean_ctor_get(v___x_1412_, 0);
                                v_isSharedCheck_1461_ = (!lean_is_exclusive(v___x_1412_)) as u8;
                                if v_isSharedCheck_1461_ == 0 {
                                    v___x_1456_ = v___x_1412_;
                                    v_isShared_1457_ = v_isSharedCheck_1461_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_inc(v_a_1454_);
                                    lean_dec(v___x_1412_);
                                    v___x_1456_ = lean_box(0);
                                    v_isShared_1457_ = v_isSharedCheck_1461_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_envLinterModule_1236_, 1);
                            v_a_1462_ = lean_ctor_get(v___x_1410_, 0);
                            v_isSharedCheck_1469_ = (!lean_is_exclusive(v___x_1410_)) as u8;
                            if v_isSharedCheck_1469_ == 0 {
                                v___x_1464_ = v___x_1410_;
                                v_isShared_1465_ = v_isSharedCheck_1469_;
                                state = 29;
                                continue;
                            } else {
                                lean_inc(v_a_1462_);
                                lean_dec(v___x_1410_);
                                v___x_1464_ = lean_box(0);
                                v_isShared_1465_ = v_isSharedCheck_1469_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_envLinterModule_1236_, 1);
                        v_a_1470_ = lean_ctor_get(v___x_1240_, 0);
                        v_isSharedCheck_1477_ = (!lean_is_exclusive(v___x_1240_)) as u8;
                        if v_isSharedCheck_1477_ == 0 {
                            v___x_1472_ = v___x_1240_;
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_1470_);
                            lean_dec(v___x_1240_);
                            v___x_1472_ = lean_box(0);
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1183_ = 1usize;
                v___x_1184_ = lean_usize_add(v_i_1178_, v___x_1183_);
                v_i_1178_ = v___x_1184_;
                v_b_1179_ = v_a_1182_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1188_ = l_Lean_MessageData_toString(v_msg_1187_);
                v___x_1189_ = lean_mk_io_user_error(v___x_1188_);
                v___x_1190_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1190_, 0, v___x_1189_);
                return v___x_1190_;
            }
            3 => {
                if lean_obj_tag(v_a_1192_) == 0 {
                    v_msg_1193_ = lean_ctor_get(v_a_1192_, 1);
                    lean_inc_ref(v_msg_1193_);
                    lean_dec_ref_known(v_a_1192_, 2);
                    v_msg_1187_ = v_msg_1193_;
                    state = 2;
                    continue;
                } else {
                    v_id_1194_ = lean_ctor_get(v_a_1192_, 0);
                    lean_inc(v_id_1194_);
                    lean_dec_ref_known(v_a_1192_, 2);
                    v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0;
                    v___x_1196_ = l_Nat_reprFast(v_id_1194_);
                    v___x_1197_ = lean_string_append(v___x_1195_, v___x_1196_);
                    lean_dec_ref(v___x_1196_);
                    v___x_1198_ = lean_mk_io_user_error(v___x_1197_);
                    v___x_1199_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1199_, 0, v___x_1198_);
                    return v___x_1199_;
                }
            }
            4 => {
                v___x_1207_ = lean_st_ref_get(v___y_1205_);
                lean_dec(v___y_1205_);
                lean_dec(v___x_1207_);
                if v___y_1204_ == 0 {
                    if v_a_1206_ == 0 {
                        v_a_1182_ = v_b_1179_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1182_ = v_anyFailed_1202_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1182_ = v_anyFailed_1202_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1219_ = 1;
                v___x_1220_ = l_Lean_Linter_EnvLinter_formatLinterResults(
                    v___y_1209_,
                    v___y_1214_,
                    v_anyFailed_1202_,
                    v___y_1216_,
                    v___y_1218_,
                    v___x_1219_,
                    v___y_1213_,
                    v_anyFailed_1202_,
                    v___y_1215_,
                    v___y_1210_,
                );
                lean_dec(v___y_1210_);
                lean_dec_ref(v___y_1215_);
                lean_dec_ref(v___y_1214_);
                if lean_obj_tag(v___x_1220_) == 0 {
                    v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
                    lean_inc(v_a_1221_);
                    lean_dec_ref_known(v___x_1220_, 1);
                    v___x_1222_ = l_Lean_MessageData_toString(v_a_1221_);
                    v___x_1223_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v___x_1222_);
                    if lean_obj_tag(v___x_1223_) == 0 {
                        lean_dec_ref_known(v___x_1223_, 1);
                        v___y_1204_ = v___y_1212_;
                        v___y_1205_ = v___y_1217_;
                        v_a_1206_ = v___y_1211_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___y_1217_);
                        v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
                        v_isSharedCheck_1233_ = (!lean_is_exclusive(v___x_1223_)) as u8;
                        if v_isSharedCheck_1233_ == 0 {
                            v___x_1226_ = v___x_1223_;
                            v_isShared_1227_ = v_isSharedCheck_1233_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1224_);
                            lean_dec(v___x_1223_);
                            v___x_1226_ = lean_box(0);
                            v_isShared_1227_ = v_isSharedCheck_1233_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1217_);
                    v_a_1234_ = lean_ctor_get(v___x_1220_, 0);
                    lean_inc(v_a_1234_);
                    lean_dec_ref_known(v___x_1220_, 1);
                    v_a_1192_ = v_a_1234_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_1228_ = lean_io_error_to_string(v_a_1224_);
                if v_isShared_1227_ == 0 {
                    lean_ctor_set_tag(v___x_1226_, 3);
                    lean_ctor_set(v___x_1226_, 0, v___x_1228_);
                    v___x_1230_ = v___x_1226_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1232_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1228_);
                    v___x_1230_ = v_reuseFailAlloc_1232_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1231_ = l_Lean_MessageData_ofFormat(v___x_1230_);
                v_msg_1187_ = v___x_1231_;
                state = 2;
                continue;
            }
            8 => {
                if v___y_1250_ == 0 {
                    lean_dec_ref(v___y_1248_);
                    lean_dec(v___y_1247_);
                    lean_dec_ref(v___y_1246_);
                    lean_dec(v___y_1244_);
                    lean_dec_ref(v___y_1243_);
                    if v___y_1245_ == 0 {
                        v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5;
                        lean_inc(v_a_1241_);
                        v___x_1252_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_a_1241_,
                                v_anyFailed_1202_,
                            );
                        v___x_1253_ = lean_string_append(v___x_1251_, v___x_1252_);
                        lean_dec_ref(v___x_1252_);
                        v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6;
                        v___x_1255_ = lean_string_append(v___x_1253_, v___x_1254_);
                        v___x_1256_ =
                            l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v___x_1255_);
                        if lean_obj_tag(v___x_1256_) == 0 {
                            lean_dec_ref_known(v___x_1256_, 1);
                            v___y_1204_ = v___y_1245_;
                            v___y_1205_ = v___y_1249_;
                            v_a_1206_ = v___y_1250_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___y_1249_);
                            v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
                            v_isSharedCheck_1266_ = (!lean_is_exclusive(v___x_1256_)) as u8;
                            if v_isSharedCheck_1266_ == 0 {
                                v___x_1259_ = v___x_1256_;
                                v_isShared_1260_ = v_isSharedCheck_1266_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1257_);
                                lean_dec(v___x_1256_);
                                v___x_1259_ = lean_box(0);
                                v_isShared_1260_ = v_isSharedCheck_1266_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        v___y_1204_ = v___y_1245_;
                        v___y_1205_ = v___y_1249_;
                        v_a_1206_ = v___y_1250_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7;
                    lean_inc(v_a_1241_);
                    v___x_1268_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_a_1241_,
                        v___y_1250_,
                    );
                    v___x_1269_ = lean_string_append(v___x_1267_, v___x_1268_);
                    lean_dec_ref(v___x_1268_);
                    if v___y_1175_ == 0 {
                        v___x_1270_ = 2;
                        v___y_1209_ = v___y_1243_;
                        v___y_1210_ = v___y_1244_;
                        v___y_1211_ = v___y_1250_;
                        v___y_1212_ = v___y_1245_;
                        v___y_1213_ = v___y_1247_;
                        v___y_1214_ = v___y_1246_;
                        v___y_1215_ = v___y_1248_;
                        v___y_1216_ = v___x_1269_;
                        v___y_1217_ = v___y_1249_;
                        v___y_1218_ = v___x_1270_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1209_ = v___y_1243_;
                        v___y_1210_ = v___y_1244_;
                        v___y_1211_ = v___y_1250_;
                        v___y_1212_ = v___y_1245_;
                        v___y_1213_ = v___y_1247_;
                        v___y_1214_ = v___y_1246_;
                        v___y_1215_ = v___y_1248_;
                        v___y_1216_ = v___x_1269_;
                        v___y_1217_ = v___y_1249_;
                        v___y_1218_ = v_scope_1173_;
                        state = 5;
                        continue;
                    }
                }
            }
            9 => {
                v___x_1261_ = lean_io_error_to_string(v_a_1257_);
                if v_isShared_1260_ == 0 {
                    lean_ctor_set_tag(v___x_1259_, 3);
                    lean_ctor_set(v___x_1259_, 0, v___x_1261_);
                    v___x_1263_ = v___x_1259_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1265_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1261_);
                    v___x_1263_ = v_reuseFailAlloc_1265_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1264_ = l_Lean_MessageData_ofFormat(v___x_1263_);
                v_msg_1187_ = v___x_1264_;
                state = 2;
                continue;
            }
            11 => {
                v_fileName_1280_ = lean_ctor_get(v___y_1278_, 0);
                v_fileMap_1281_ = lean_ctor_get(v___y_1278_, 1);
                v_currRecDepth_1282_ = lean_ctor_get(v___y_1278_, 3);
                v_ref_1283_ = lean_ctor_get(v___y_1278_, 5);
                v_currNamespace_1284_ = lean_ctor_get(v___y_1278_, 6);
                v_openDecls_1285_ = lean_ctor_get(v___y_1278_, 7);
                v_initHeartbeats_1286_ = lean_ctor_get(v___y_1278_, 8);
                v_maxHeartbeats_1287_ = lean_ctor_get(v___y_1278_, 9);
                v_quotContext_1288_ = lean_ctor_get(v___y_1278_, 10);
                v_currMacroScope_1289_ = lean_ctor_get(v___y_1278_, 11);
                v_cancelTk_x3f_1290_ = lean_ctor_get(v___y_1278_, 12);
                v_suppressElabErrors_1291_ = lean_ctor_get_uint8(
                    v___y_1278_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1292_ = lean_ctor_get(v___y_1278_, 13);
                v_isSharedCheck_1332_ = (!lean_is_exclusive(v___y_1278_)) as u8;
                if v_isSharedCheck_1332_ == 0 {
                    v_unused_1333_ = lean_ctor_get(v___y_1278_, 4);
                    lean_dec(v_unused_1333_);
                    v_unused_1334_ = lean_ctor_get(v___y_1278_, 2);
                    lean_dec(v_unused_1334_);
                    v___x_1294_ = v___y_1278_;
                    v_isShared_1295_ = v_isSharedCheck_1332_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_1292_);
                    lean_inc(v_cancelTk_x3f_1290_);
                    lean_inc(v_currMacroScope_1289_);
                    lean_inc(v_quotContext_1288_);
                    lean_inc(v_maxHeartbeats_1287_);
                    lean_inc(v_initHeartbeats_1286_);
                    lean_inc(v_openDecls_1285_);
                    lean_inc(v_currNamespace_1284_);
                    lean_inc(v_ref_1283_);
                    lean_inc(v_currRecDepth_1282_);
                    lean_inc(v_fileMap_1281_);
                    lean_inc(v_fileName_1280_);
                    lean_dec(v___y_1278_);
                    v___x_1294_ = lean_box(0);
                    v_isShared_1295_ = v_isSharedCheck_1332_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1296_ =
                    l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___y_1276_, v___y_1279_);
                lean_dec(v___y_1276_);
                if lean_obj_tag(v___x_1296_) == 0 {
                    v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
                    lean_inc(v_a_1297_);
                    lean_dec_ref_known(v___x_1296_, 1);
                    v___x_1298_ = l_Lean_maxRecDepth;
                    v___x_1299_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5(
                        v___y_1272_,
                        v___x_1298_,
                    );
                    if v_isShared_1295_ == 0 {
                        lean_ctor_set(v___x_1294_, 4, v___x_1299_);
                        lean_ctor_set(v___x_1294_, 2, v___y_1272_);
                        v___x_1301_ = v___x_1294_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 14, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_fileName_1280_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_fileMap_1281_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 2, v___y_1272_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_currRecDepth_1282_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 4, v___x_1299_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 5, v_ref_1283_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 6, v_currNamespace_1284_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 7, v_openDecls_1285_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 8, v_initHeartbeats_1286_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 9, v_maxHeartbeats_1287_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 10, v_quotContext_1288_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 11, v_currMacroScope_1289_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 12, v_cancelTk_x3f_1290_);
                        lean_ctor_set(v_reuseFailAlloc_1330_, 13, v_inheritedTraceOptions_1292_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1330_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_1291_,
                        );
                        v___x_1301_ = v_reuseFailAlloc_1330_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1294_);
                    lean_dec_ref(v_inheritedTraceOptions_1292_);
                    lean_dec(v_cancelTk_x3f_1290_);
                    lean_dec(v_currMacroScope_1289_);
                    lean_dec(v_quotContext_1288_);
                    lean_dec(v_maxHeartbeats_1287_);
                    lean_dec(v_initHeartbeats_1286_);
                    lean_dec(v_openDecls_1285_);
                    lean_dec(v_currNamespace_1284_);
                    lean_dec(v_ref_1283_);
                    lean_dec(v_currRecDepth_1282_);
                    lean_dec_ref(v_fileMap_1281_);
                    lean_dec_ref(v_fileName_1280_);
                    lean_dec(v___y_1279_);
                    lean_dec(v___y_1277_);
                    lean_dec_ref(v___y_1272_);
                    v_a_1331_ = lean_ctor_get(v___x_1296_, 0);
                    lean_inc(v_a_1331_);
                    lean_dec_ref_known(v___x_1296_, 1);
                    v_a_1192_ = v_a_1331_;
                    state = 3;
                    continue;
                }
            }
            13 => {
                lean_ctor_set_uint8(
                    v___x_1301_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_1273_,
                );
                v___x_1302_ = l_Lean_Linter_EnvLinter_getChecks(
                    v_scope_1173_,
                    v___y_1174_,
                    v___x_1301_,
                    v___y_1279_,
                );
                if lean_obj_tag(v___x_1302_) == 0 {
                    v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
                    lean_inc(v_a_1303_);
                    lean_dec_ref_known(v___x_1302_, 1);
                    v___x_1304_ = lean_array_get_size(v_a_1303_);
                    v___x_1305_ = lean_nat_dec_eq(v___x_1304_, v___x_1200_);
                    if v___x_1305_ == 0 {
                        v___x_1306_ = l_Lean_Linter_EnvLinter_lintCore(
                            v_a_1297_,
                            v_a_1303_,
                            v___x_1301_,
                            v___y_1279_,
                        );
                        if lean_obj_tag(v___x_1306_) == 0 {
                            v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
                            lean_inc(v_a_1307_);
                            lean_dec_ref_known(v___x_1306_, 1);
                            v___x_1308_ = lean_array_get_size(v_a_1307_);
                            v___x_1309_ = lean_nat_dec_lt(v___x_1200_, v___x_1308_);
                            if v___x_1309_ == 0 {
                                v___y_1243_ = v_a_1307_;
                                v___y_1244_ = v___y_1279_;
                                v___y_1245_ = v___y_1275_;
                                v___y_1246_ = v_a_1297_;
                                v___y_1247_ = v___x_1304_;
                                v___y_1248_ = v___x_1301_;
                                v___y_1249_ = v___y_1277_;
                                v___y_1250_ = v___x_1305_;
                                state = 8;
                                continue;
                            } else {
                                if v___x_1309_ == 0 {
                                    v___y_1243_ = v_a_1307_;
                                    v___y_1244_ = v___y_1279_;
                                    v___y_1245_ = v___y_1275_;
                                    v___y_1246_ = v_a_1297_;
                                    v___y_1247_ = v___x_1304_;
                                    v___y_1248_ = v___x_1301_;
                                    v___y_1249_ = v___y_1277_;
                                    v___y_1250_ = v___x_1305_;
                                    state = 8;
                                    continue;
                                } else {
                                    v___x_1310_ = lean_usize_of_nat(v___x_1308_);
                                    v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6(v___x_1304_, v_a_1307_, v___y_1274_, v___x_1310_);
                                    v___y_1243_ = v_a_1307_;
                                    v___y_1244_ = v___y_1279_;
                                    v___y_1245_ = v___y_1275_;
                                    v___y_1246_ = v_a_1297_;
                                    v___y_1247_ = v___x_1304_;
                                    v___y_1248_ = v___x_1301_;
                                    v___y_1249_ = v___y_1277_;
                                    v___y_1250_ = v___x_1311_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1301_);
                            lean_dec(v_a_1297_);
                            lean_dec(v___y_1279_);
                            lean_dec(v___y_1277_);
                            v_a_1312_ = lean_ctor_get(v___x_1306_, 0);
                            lean_inc(v_a_1312_);
                            lean_dec_ref_known(v___x_1306_, 1);
                            v_a_1192_ = v_a_1312_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1303_);
                        lean_dec_ref(v___x_1301_);
                        lean_dec(v_a_1297_);
                        lean_dec(v___y_1279_);
                        v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8;
                        lean_inc(v_a_1241_);
                        v___x_1314_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_a_1241_,
                                v___x_1305_,
                            );
                        v___x_1315_ = lean_string_append(v___x_1313_, v___x_1314_);
                        lean_dec_ref(v___x_1314_);
                        v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6;
                        v___x_1317_ = lean_string_append(v___x_1315_, v___x_1316_);
                        v___x_1318_ =
                            l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v___x_1317_);
                        if lean_obj_tag(v___x_1318_) == 0 {
                            lean_dec_ref_known(v___x_1318_, 1);
                            v___y_1204_ = v___y_1275_;
                            v___y_1205_ = v___y_1277_;
                            v_a_1206_ = v_anyFailed_1201_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___y_1277_);
                            v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
                            v_isSharedCheck_1328_ = (!lean_is_exclusive(v___x_1318_)) as u8;
                            if v_isSharedCheck_1328_ == 0 {
                                v___x_1321_ = v___x_1318_;
                                v_isShared_1322_ = v_isSharedCheck_1328_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_1319_);
                                lean_dec(v___x_1318_);
                                v___x_1321_ = lean_box(0);
                                v_isShared_1322_ = v_isSharedCheck_1328_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1301_);
                    lean_dec(v_a_1297_);
                    lean_dec(v___y_1279_);
                    lean_dec(v___y_1277_);
                    v_a_1329_ = lean_ctor_get(v___x_1302_, 0);
                    lean_inc(v_a_1329_);
                    lean_dec_ref_known(v___x_1302_, 1);
                    v_a_1192_ = v_a_1329_;
                    state = 3;
                    continue;
                }
            }
            14 => {
                v___x_1323_ = lean_io_error_to_string(v_a_1319_);
                if v_isShared_1322_ == 0 {
                    lean_ctor_set_tag(v___x_1321_, 3);
                    lean_ctor_set(v___x_1321_, 0, v___x_1323_);
                    v___x_1325_ = v___x_1321_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1323_);
                    v___x_1325_ = v_reuseFailAlloc_1327_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_1326_ = l_Lean_MessageData_ofFormat(v___x_1325_);
                v_msg_1187_ = v___x_1326_;
                state = 2;
                continue;
            }
            16 => {
                if v___y_1344_ == 0 {
                    v___x_1345_ = lean_st_ref_take(v___y_1343_);
                    v_env_1346_ = lean_ctor_get(v___x_1345_, 0);
                    v_nextMacroScope_1347_ = lean_ctor_get(v___x_1345_, 1);
                    v_ngen_1348_ = lean_ctor_get(v___x_1345_, 2);
                    v_auxDeclNGen_1349_ = lean_ctor_get(v___x_1345_, 3);
                    v_traceState_1350_ = lean_ctor_get(v___x_1345_, 4);
                    v_messages_1351_ = lean_ctor_get(v___x_1345_, 6);
                    v_infoState_1352_ = lean_ctor_get(v___x_1345_, 7);
                    v_snapshotTasks_1353_ = lean_ctor_get(v___x_1345_, 8);
                    v_isSharedCheck_1362_ = (!lean_is_exclusive(v___x_1345_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v_unused_1363_ = lean_ctor_get(v___x_1345_, 5);
                        lean_dec(v_unused_1363_);
                        v___x_1355_ = v___x_1345_;
                        v_isShared_1356_ = v_isSharedCheck_1362_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1353_);
                        lean_inc(v_infoState_1352_);
                        lean_inc(v_messages_1351_);
                        lean_inc(v_traceState_1350_);
                        lean_inc(v_auxDeclNGen_1349_);
                        lean_inc(v_ngen_1348_);
                        lean_inc(v_nextMacroScope_1347_);
                        lean_inc(v_env_1346_);
                        lean_dec(v___x_1345_);
                        v___x_1355_ = lean_box(0);
                        v_isShared_1356_ = v_isSharedCheck_1362_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_inc(v___y_1343_);
                    v___y_1272_ = v___y_1336_;
                    v___y_1273_ = v___y_1339_;
                    v___y_1274_ = v___y_1340_;
                    v___y_1275_ = v___y_1341_;
                    v___y_1276_ = v___y_1342_;
                    v___y_1277_ = v___y_1343_;
                    v___y_1278_ = v___y_1338_;
                    v___y_1279_ = v___y_1343_;
                    state = 11;
                    continue;
                }
            }
            17 => {
                v___x_1357_ = l_Lean_Kernel_enableDiag(v_env_1346_, v___y_1339_);
                lean_inc_ref(v___y_1337_);
                if v_isShared_1356_ == 0 {
                    lean_ctor_set(v___x_1355_, 5, v___y_1337_);
                    lean_ctor_set(v___x_1355_, 0, v___x_1357_);
                    v___x_1359_ = v___x_1355_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1357_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_nextMacroScope_1347_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_ngen_1348_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_auxDeclNGen_1349_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_traceState_1350_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 5, v___y_1337_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 6, v_messages_1351_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 7, v_infoState_1352_);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 8, v_snapshotTasks_1353_);
                    v___x_1359_ = v_reuseFailAlloc_1361_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_1360_ = lean_st_ref_set(v___y_1343_, v___x_1359_);
                lean_inc(v___y_1343_);
                v___y_1272_ = v___y_1336_;
                v___y_1273_ = v___y_1339_;
                v___y_1274_ = v___y_1340_;
                v___y_1275_ = v___y_1341_;
                v___y_1276_ = v___y_1342_;
                v___y_1277_ = v___y_1343_;
                v___y_1278_ = v___y_1338_;
                v___y_1279_ = v___y_1343_;
                state = 11;
                continue;
            }
            19 => {
                v___x_1370_ = lean_box(0);
                v_sz_1371_ = lean_array_size(v___y_1366_);
                v___x_1372_ = 0usize;
                v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_1171_, v___y_1366_, v_sz_1371_, v___x_1372_, v___x_1370_);
                lean_dec_ref(v___y_1366_);
                if lean_obj_tag(v___x_1373_) == 0 {
                    lean_dec_ref_known(v___x_1373_, 1);
                    v___x_1374_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13);
                    v___x_1375_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14);
                    v___x_1376_ = lean_io_get_num_heartbeats();
                    v___x_1377_ = l_Lean_firstFrontendMacroScope;
                    v___x_1378_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15);
                    v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18;
                    v___x_1380_ = lean_box(0);
                    v___x_1381_ = lean_box(0);
                    v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19;
                    v___x_1383_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20);
                    v___x_1384_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21);
                    v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22;
                    v___x_1386_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v___x_1386_, 0, v___y_1368_);
                    lean_ctor_set(v___x_1386_, 1, v___x_1378_);
                    lean_ctor_set(v___x_1386_, 2, v___x_1379_);
                    lean_ctor_set(v___x_1386_, 3, v___x_1382_);
                    lean_ctor_set(v___x_1386_, 4, v___x_1383_);
                    lean_ctor_set(v___x_1386_, 5, v___x_1374_);
                    lean_ctor_set(v___x_1386_, 6, v___x_1375_);
                    lean_ctor_set(v___x_1386_, 7, v___x_1384_);
                    lean_ctor_set(v___x_1386_, 8, v___x_1385_);
                    v___x_1387_ = lean_st_mk_ref(v___x_1386_);
                    v___x_1388_ = l_Lean_inheritedTraceOptions;
                    v___x_1389_ = lean_st_ref_get(v___x_1388_);
                    v___x_1390_ = lean_st_ref_get(v___x_1387_);
                    v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23;
                    v___x_1392_ = l_Lean_instInhabitedFileMap_default;
                    v___x_1393_ = lean_unsigned_to_nat(1000);
                    v___x_1394_ = lean_box(0);
                    v___x_1395_ = l_Lean_Core_getMaxHeartbeats(v___y_1365_);
                    v___x_1396_ = lean_box(0);
                    lean_inc_ref(v___y_1365_);
                    v___x_1397_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v___x_1397_, 0, v___x_1391_);
                    lean_ctor_set(v___x_1397_, 1, v___x_1392_);
                    lean_ctor_set(v___x_1397_, 2, v___y_1365_);
                    lean_ctor_set(v___x_1397_, 3, v___x_1200_);
                    lean_ctor_set(v___x_1397_, 4, v___x_1393_);
                    lean_ctor_set(v___x_1397_, 5, v___x_1394_);
                    lean_ctor_set(v___x_1397_, 6, v___x_1380_);
                    lean_ctor_set(v___x_1397_, 7, v___x_1381_);
                    lean_ctor_set(v___x_1397_, 8, v___x_1376_);
                    lean_ctor_set(v___x_1397_, 9, v___x_1395_);
                    lean_ctor_set(v___x_1397_, 10, v___x_1380_);
                    lean_ctor_set(v___x_1397_, 11, v___x_1377_);
                    lean_ctor_set(v___x_1397_, 12, v___x_1396_);
                    lean_ctor_set(v___x_1397_, 13, v___x_1389_);
                    lean_ctor_set_uint8(
                        v___x_1397_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_anyFailed_1201_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1397_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_anyFailed_1201_,
                    );
                    v_env_1398_ = lean_ctor_get(v___x_1390_, 0);
                    lean_inc_ref(v_env_1398_);
                    lean_dec(v___x_1390_);
                    v___x_1399_ = l_Lean_diagnostics;
                    v___x_1400_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4(
                        v___y_1365_,
                        v___x_1399_,
                    );
                    v___x_1401_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1398_);
                    lean_dec_ref(v_env_1398_);
                    if v___x_1401_ == 0 {
                        if v___x_1400_ == 0 {
                            v___y_1336_ = v___y_1365_;
                            v___y_1337_ = v___x_1374_;
                            v___y_1338_ = v___x_1397_;
                            v___y_1339_ = v___x_1400_;
                            v___y_1340_ = v___x_1372_;
                            v___y_1341_ = v___y_1369_;
                            v___y_1342_ = v___y_1367_;
                            v___y_1343_ = v___x_1387_;
                            v___y_1344_ = v___x_1237_;
                            state = 16;
                            continue;
                        } else {
                            v___y_1336_ = v___y_1365_;
                            v___y_1337_ = v___x_1374_;
                            v___y_1338_ = v___x_1397_;
                            v___y_1339_ = v___x_1400_;
                            v___y_1340_ = v___x_1372_;
                            v___y_1341_ = v___y_1369_;
                            v___y_1342_ = v___y_1367_;
                            v___y_1343_ = v___x_1387_;
                            v___y_1344_ = v___x_1401_;
                            state = 16;
                            continue;
                        }
                    } else {
                        v___y_1336_ = v___y_1365_;
                        v___y_1337_ = v___x_1374_;
                        v___y_1338_ = v___x_1397_;
                        v___y_1339_ = v___x_1400_;
                        v___y_1340_ = v___x_1372_;
                        v___y_1341_ = v___y_1369_;
                        v___y_1342_ = v___y_1367_;
                        v___y_1343_ = v___x_1387_;
                        v___y_1344_ = v___x_1400_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_1368_);
                    lean_dec(v___y_1367_);
                    lean_dec_ref(v___y_1365_);
                    v_a_1402_ = lean_ctor_get(v___x_1373_, 0);
                    v_isSharedCheck_1409_ = (!lean_is_exclusive(v___x_1373_)) as u8;
                    if v_isSharedCheck_1409_ == 0 {
                        v___x_1404_ = v___x_1373_;
                        v_isShared_1405_ = v_isSharedCheck_1409_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_1402_);
                        lean_dec(v___x_1373_);
                        v___x_1404_ = lean_box(0);
                        v_isShared_1405_ = v_isSharedCheck_1409_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_1405_ == 0 {
                    v___x_1407_ = v___x_1404_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
                    v___x_1407_ = v_reuseFailAlloc_1408_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1407_;
            }
            22 => {
                v___x_1419_ = lean_unbox_usize(v_snd_1415_);
                lean_dec(v_snd_1415_);
                v___x_1420_ = lean_compacted_region_free(v___x_1419_);
                if lean_obj_tag(v___x_1420_) == 0 {
                    lean_dec_ref_known(v___x_1420_, 1);
                    lean_inc(v_a_1241_);
                    v___x_1421_ = lean_alloc_ctor(0, 1, (3) as u32);
                    lean_ctor_set(v___x_1421_, 0, v_a_1241_);
                    lean_ctor_set_uint8(
                        v___x_1421_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_anyFailed_1201_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1421_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_anyFailed_1202_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1421_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_anyFailed_1201_,
                    );
                    v___x_1422_ = lean_unsigned_to_nat(2);
                    v___x_1423_ = lean_mk_empty_array_with_capacity(v___x_1422_);
                    v___x_1424_ = lean_array_push(v___x_1423_, v___x_1421_);
                    v___x_1425_ = lean_array_push(v___x_1424_, v_envLinterModule_1236_);
                    v___x_1426_ = l_Lean_Options_empty;
                    v___x_1427_ = 1024;
                    v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24;
                    v___x_1429_ = lean_box(1);
                    v___x_1430_ = l_Lean_importModules(
                        v___x_1425_,
                        v___x_1426_,
                        v___x_1427_,
                        v___x_1428_,
                        v_anyFailed_1201_,
                        v_anyFailed_1202_,
                        v___y_1418_,
                        v___x_1429_,
                    );
                    if lean_obj_tag(v___x_1430_) == 0 {
                        v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
                        lean_inc(v_a_1431_);
                        lean_dec_ref_known(v___x_1430_, 1);
                        v___x_1432_ = l_Lean_Name_getRoot(v_a_1241_);
                        v___x_1433_ =
                            l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(
                                v_a_1431_,
                                v_args_1172_,
                                v___x_1432_,
                            );
                        v___x_1434_ = lean_array_get_size(v___x_1433_);
                        v___x_1435_ = lean_nat_dec_eq(v___x_1434_, v___x_1200_);
                        if v___x_1435_ == 0 {
                            v___y_1365_ = v___x_1426_;
                            v___y_1366_ = v___x_1433_;
                            v___y_1367_ = v___x_1432_;
                            v___y_1368_ = v_a_1431_;
                            v___y_1369_ = v_anyFailed_1202_;
                            state = 19;
                            continue;
                        } else {
                            v___y_1365_ = v___x_1426_;
                            v___y_1366_ = v___x_1433_;
                            v___y_1367_ = v___x_1432_;
                            v___y_1368_ = v_a_1431_;
                            v___y_1369_ = v_anyFailed_1201_;
                            state = 19;
                            continue;
                        }
                    } else {
                        v_a_1436_ = lean_ctor_get(v___x_1430_, 0);
                        v_isSharedCheck_1443_ = (!lean_is_exclusive(v___x_1430_)) as u8;
                        if v_isSharedCheck_1443_ == 0 {
                            v___x_1438_ = v___x_1430_;
                            v_isShared_1439_ = v_isSharedCheck_1443_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_1436_);
                            lean_dec(v___x_1430_);
                            v___x_1438_ = lean_box(0);
                            v_isShared_1439_ = v_isSharedCheck_1443_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_envLinterModule_1236_, 1);
                    v_a_1444_ = lean_ctor_get(v___x_1420_, 0);
                    v_isSharedCheck_1451_ = (!lean_is_exclusive(v___x_1420_)) as u8;
                    if v_isSharedCheck_1451_ == 0 {
                        v___x_1446_ = v___x_1420_;
                        v_isShared_1447_ = v_isSharedCheck_1451_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_1444_);
                        lean_dec(v___x_1420_);
                        v___x_1446_ = lean_box(0);
                        v_isShared_1447_ = v_isSharedCheck_1451_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1439_ == 0 {
                    v___x_1441_ = v___x_1438_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
                    v___x_1441_ = v_reuseFailAlloc_1442_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1441_;
            }
            25 => {
                if v_isShared_1447_ == 0 {
                    v___x_1449_ = v___x_1446_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
                    v___x_1449_ = v_reuseFailAlloc_1450_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1449_;
            }
            27 => {
                if v_isShared_1457_ == 0 {
                    v___x_1459_ = v___x_1456_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
                    v___x_1459_ = v_reuseFailAlloc_1460_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1459_;
            }
            29 => {
                if v_isShared_1465_ == 0 {
                    v___x_1467_ = v___x_1464_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
                    v___x_1467_ = v_reuseFailAlloc_1468_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1467_;
            }
            31 => {
                if v_isShared_1473_ == 0 {
                    v___x_1475_ = v___x_1472_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
                    v___x_1475_ = v_reuseFailAlloc_1476_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___boxed(
    mut v___x_1478_: *mut LeanObject,
    mut v_args_1479_: *mut LeanObject,
    mut v_scope_1480_: *mut LeanObject,
    mut v___y_1481_: *mut LeanObject,
    mut v___y_1482_: *mut LeanObject,
    mut v_as_1483_: *mut LeanObject,
    mut v_sz_1484_: *mut LeanObject,
    mut v_i_1485_: *mut LeanObject,
    mut v_b_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_scope_boxed_1488_: u8 = 0;
    let mut v___y_11198__boxed_1489_: u8 = 0;
    let mut v_sz_boxed_1490_: usize = 0;
    let mut v_i_boxed_1491_: usize = 0;
    let mut v_b_boxed_1492_: u8 = 0;
    let mut v_res_1493_: *mut LeanObject = core::ptr::null_mut();
    v_scope_boxed_1488_ = (lean_unbox(v_scope_1480_) as u8);
    v___y_11198__boxed_1489_ = (lean_unbox(v___y_1482_) as u8);
    v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1484_);
    lean_dec(v_sz_1484_);
    v_i_boxed_1491_ = lean_unbox_usize(v_i_1485_);
    lean_dec(v_i_1485_);
    v_b_boxed_1492_ = (lean_unbox(v_b_1486_) as u8);
    v_res_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7(v___x_1478_, v_args_1479_, v_scope_boxed_1488_, v___y_1481_, v___y_11198__boxed_1489_, v_as_1483_, v_sz_boxed_1490_, v_i_boxed_1491_, v_b_boxed_1492_);
    lean_dec_ref(v_as_1483_);
    lean_dec(v___y_1481_);
    lean_dec_ref(v_args_1479_);
    lean_dec(v___x_1478_);
    return v_res_1493_;
}
pub unsafe fn _init_l_Lake_BuiltinLint_run___boxed__const__1() -> *mut LeanObject {
    let mut v___x_1495_: u32 = 0;
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = 0;
    v___x_1496_ = lean_box_uint32(v___x_1495_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Lake_BuiltinLint_run___boxed__const__2() -> *mut LeanObject {
    let mut v___x_1497_: u32 = 0;
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v___x_1497_ = 1;
    v___x_1498_ = lean_box_uint32(v___x_1497_);
    return v___x_1498_;
}
pub unsafe fn l_Lake_BuiltinLint_run(mut v_args_1499_: *mut LeanObject) -> *mut LeanObject {
    let mut v_scope_1501_: u8 = 0;
    let mut v_only_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mods_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anyFailed_1506_: u8 = 0;
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___y_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1517_: u8 = 0;
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut v_a_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1531_: u8 = 0;
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1543_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut v_unused_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scope_1501_ = lean_ctor_get_uint8(
                    v_args_1499_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_only_1502_ = lean_ctor_get(v_args_1499_, 0);
                v_mods_1503_ = lean_ctor_get(v_args_1499_, 1);
                lean_inc_ref(v_mods_1503_);
                v___x_1504_ = lean_array_get_size(v_mods_1503_);
                v___x_1505_ = lean_unsigned_to_nat(0);
                v_anyFailed_1506_ = lean_nat_dec_eq(v___x_1504_, v___x_1505_);
                if v_anyFailed_1506_ == 0 {
                    v___x_1507_ = lean_array_get_size(v_only_1502_);
                    v___x_1508_ = lean_nat_dec_eq(v___x_1507_, v___x_1505_);
                    if v___x_1508_ == 0 {
                        lean_inc_ref(v_only_1502_);
                        v___x_1536_ = lean_array_to_list(v_only_1502_);
                        v___x_1537_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                        v___y_1510_ = v___x_1537_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1538_ = lean_box(0);
                        v___y_1510_ = v___x_1538_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mods_1503_);
                    lean_dec_ref(v_args_1499_);
                    v___x_1539_ = l_Lake_BuiltinLint_run___closed__0;
                    v___x_1540_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8(v___x_1539_);
                    if lean_obj_tag(v___x_1540_) == 0 {
                        v_isSharedCheck_1548_ = (!lean_is_exclusive(v___x_1540_)) as u8;
                        if v_isSharedCheck_1548_ == 0 {
                            v_unused_1549_ = lean_ctor_get(v___x_1540_, 0);
                            lean_dec(v_unused_1549_);
                            v___x_1542_ = v___x_1540_;
                            v_isShared_1543_ = v_isSharedCheck_1548_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_1540_);
                            v___x_1542_ = lean_box(0);
                            v_isShared_1543_ = v_isSharedCheck_1548_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_1550_ = lean_ctor_get(v___x_1540_, 0);
                        v_isSharedCheck_1557_ = (!lean_is_exclusive(v___x_1540_)) as u8;
                        if v_isSharedCheck_1557_ == 0 {
                            v___x_1552_ = v___x_1540_;
                            v_isShared_1553_ = v_isSharedCheck_1557_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1550_);
                            lean_dec(v___x_1540_);
                            v___x_1552_ = lean_box(0);
                            v_isShared_1553_ = v_isSharedCheck_1557_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_1511_ = lean_array_size(v_mods_1503_);
                v___x_1512_ = 0usize;
                v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7(v___x_1504_, v_args_1499_, v_scope_1501_, v___y_1510_, v___x_1508_, v_mods_1503_, v_sz_1511_, v___x_1512_, v_anyFailed_1506_);
                lean_dec_ref(v_mods_1503_);
                lean_dec(v___y_1510_);
                lean_dec_ref(v_args_1499_);
                if lean_obj_tag(v___x_1513_) == 0 {
                    v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
                    v_isSharedCheck_1527_ = (!lean_is_exclusive(v___x_1513_)) as u8;
                    if v_isSharedCheck_1527_ == 0 {
                        v___x_1516_ = v___x_1513_;
                        v_isShared_1517_ = v_isSharedCheck_1527_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1514_);
                        lean_dec(v___x_1513_);
                        v___x_1516_ = lean_box(0);
                        v_isShared_1517_ = v_isSharedCheck_1527_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1528_ = lean_ctor_get(v___x_1513_, 0);
                    v_isSharedCheck_1535_ = (!lean_is_exclusive(v___x_1513_)) as u8;
                    if v_isSharedCheck_1535_ == 0 {
                        v___x_1530_ = v___x_1513_;
                        v_isShared_1531_ = v_isSharedCheck_1535_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1528_);
                        lean_dec(v___x_1513_);
                        v___x_1530_ = lean_box(0);
                        v_isShared_1531_ = v_isSharedCheck_1535_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1518_ = (lean_unbox(v_a_1514_) as u8);
                lean_dec(v_a_1514_);
                if v___x_1518_ == 0 {
                    v___x_1519_ = l_Lake_BuiltinLint_run___boxed__const__1;
                    if v_isShared_1517_ == 0 {
                        lean_ctor_set(v___x_1516_, 0, v___x_1519_);
                        v___x_1521_ = v___x_1516_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
                        v___x_1521_ = v_reuseFailAlloc_1522_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1523_ = l_Lake_BuiltinLint_run___boxed__const__2;
                    if v_isShared_1517_ == 0 {
                        lean_ctor_set(v___x_1516_, 0, v___x_1523_);
                        v___x_1525_ = v___x_1516_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
                        v___x_1525_ = v_reuseFailAlloc_1526_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1521_;
            }
            4 => {
                return v___x_1525_;
            }
            5 => {
                if v_isShared_1531_ == 0 {
                    v___x_1533_ = v___x_1530_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
                    v___x_1533_ = v_reuseFailAlloc_1534_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1533_;
            }
            7 => {
                v___x_1544_ = l_Lake_BuiltinLint_run___boxed__const__2;
                if v_isShared_1543_ == 0 {
                    lean_ctor_set(v___x_1542_, 0, v___x_1544_);
                    v___x_1546_ = v___x_1542_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
                    v___x_1546_ = v_reuseFailAlloc_1547_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1546_;
            }
            9 => {
                if v_isShared_1553_ == 0 {
                    v___x_1555_ = v___x_1552_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
                    v___x_1555_ = v_reuseFailAlloc_1556_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuiltinLint_run___boxed(
    mut v_args_1558_: *mut LeanObject,
    mut v_a_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Lake_BuiltinLint_run(v_args_1558_);
    return v_res_1560_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI_BuiltinLint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_EnvLinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_BuiltinLint_run___boxed__const__1 = _init_l_Lake_BuiltinLint_run___boxed__const__1();
    lean_mark_persistent(l_Lake_BuiltinLint_run___boxed__const__1);
    l_Lake_BuiltinLint_run___boxed__const__2 = _init_l_Lake_BuiltinLint_run___boxed__const__2();
    lean_mark_persistent(l_Lake_BuiltinLint_run___boxed__const__2);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI_BuiltinLint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI_BuiltinLint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_EnvLinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_PersistentLintLog(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_BuiltinLint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_CLI_BuiltinLint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_CLI_BuiltinLint(builtin);
}
