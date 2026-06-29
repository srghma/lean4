// Lean compiler output
// Module: Lean.Linter.EnvLinter.Frontend
// Imports: Lean.Linter.EnvLinter.Basic Lean.DeclarationRange Lean.Util.Path Lean.CoreM Lean.Elab.Command
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop, l_Array_instInhabited,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::l_Lean_ParametricAttribute_getParam_x3f___redArg;
use crate::r#gen::Lean::AuxRecursor::{l_Lean_isAuxRecursor, l_Lean_isNoConfusion};
use crate::r#gen::Lean::CoreM::{
    initialize_Lean_CoreM, l_Lean_Core_wrapAsync___redArg, runtime_initialize_Lean_CoreM,
};
use crate::r#gen::Lean::Data::DeclarationRange::l_Lean_instInhabitedDeclarationRanges_default;
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf, l_Lean_Name_lt,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::{
    initialize_Lean_DeclarationRange, l_Lean_builtinDeclRanges, l_Lean_declRangeExt,
    runtime_initialize_Lean_DeclarationRange,
};
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_mkMetaContext,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_allImportedModuleNames, l_Lean_Environment_const2ModIdx,
    l_Lean_Environment_constants, l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_findConstVal_x3f, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_header, l_Lean_Environment_mainModule, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_toMessageData, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Linter::EnvLinter::Basic::{
    initialize_Lean_Linter_EnvLinter_Basic, l_Lean_Linter_EnvLinter_envLinterExt,
    l_Lean_Linter_EnvLinter_getEnvLinter, l_Lean_Linter_EnvLinter_isAutoDecl___redArg,
    runtime_initialize_Lean_Linter_EnvLinter_Basic,
};
use crate::r#gen::Lean::Linter::EnvLinter::Nolint::l_Lean_Linter_EnvLinter_builtinNolintAttr;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_joinSep, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isRecCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Path::{
    initialize_Lean_Util_Path, l_Lean_SearchPath_findWithExt, l_Lean_getSrcSearchPath,
    l_Lean_modToFilePath, runtime_initialize_Lean_Util_Path,
};
use crate::ffi::lean_task_get_own;
use crate::ffi::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_nat_shiftr;
use crate::ffi::lean_string_dec_lt;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::ffi::lean_io_as_task;
use crate::ffi::{lean_st_mk_ref, lean_st_ref_get};
pub static mut l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default: u8 = 0;
pub static mut l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity: u8 = 0;
pub static l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value:
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
        76, 101, 97, 110, 46, 76, 105, 110, 116, 101, 114, 46, 69, 110, 118, 76, 105, 110, 116,
        101, 114, 46, 76, 105, 110, 116, 86, 101, 114, 98, 111, 115, 105, 116, 121, 46, 108, 111,
        119, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value:
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
        76, 101, 97, 110, 46, 76, 105, 110, 116, 101, 114, 46, 69, 110, 118, 76, 105, 110, 116,
        101, 114, 46, 76, 105, 110, 116, 86, 101, 114, 98, 111, 115, 105, 116, 121, 46, 109, 101,
        100, 105, 117, 109, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 76, 105, 110, 116, 101, 114, 46, 69, 110, 118, 76, 105, 110, 116,
        101, 114, 46, 76, 105, 110, 116, 86, 101, 114, 98, 111, 115, 105, 116, 121, 46, 104, 105,
        103, 104, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value:
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
    m_fun: l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_EnvLinter_instReprLintVerbosity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_EnvLinter_instInhabitedLintScope_default: u8 = 0;
pub static mut l_Lean_Linter_EnvLinter_instInhabitedLintScope: u8 = 0;
pub static l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value:
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
        76, 101, 97, 110, 46, 76, 105, 110, 116, 101, 114, 46, 69, 110, 118, 76, 105, 110, 116,
        101, 114, 46, 76, 105, 110, 116, 83, 99, 111, 112, 101, 46, 100, 101, 102, 97, 117, 108,
        116, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 76, 105, 110, 116, 101, 114, 46, 69, 110, 118, 76, 105, 110, 116,
        101, 114, 46, 76, 105, 110, 116, 83, 99, 111, 112, 101, 46, 101, 120, 116, 114, 97, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        76, 101, 97, 110, 46, 76, 105, 110, 116, 101, 114, 46, 69, 110, 118, 76, 105, 110, 116,
        101, 114, 46, 76, 105, 110, 116, 83, 99, 111, 112, 101, 46, 97, 108, 108, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value:
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
    m_fun: l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_EnvLinter_instReprLintScope___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_EnvLinter_instReprLintScope: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_getChecks___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Linter_EnvLinter_getChecks___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_getChecks___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0: u64 = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [76, 73, 78, 84, 69, 82, 32, 70, 65, 73, 76, 69, 68, 58, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_printWarning___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [35, 99, 104, 101, 99, 107, 32, 0],
};
static mut l_Lean_Linter_EnvLinter_printWarning___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_printWarning___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_printWarning___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_printWarning___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_printWarning___closed__2_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 47, 45, 32, 0],
};
static mut l_Lean_Linter_EnvLinter_printWarning___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_printWarning___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_printWarning___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_printWarning___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_printWarning___closed__4_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 45, 47, 0],
};
static mut l_Lean_Linter_EnvLinter_printWarning___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_printWarning___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_printWarning___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_printWarning___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_printWarning___closed__6_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Linter_EnvLinter_printWarning___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_printWarning___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_printWarning___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_printWarning___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_printWarning___closed__8_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [58, 32, 101, 114, 114, 111, 114, 58, 32, 0],
};
static mut l_Lean_Linter_EnvLinter_printWarning___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_printWarning___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_printWarning___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_printWarning___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_printWarning___closed__10_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Lean_Linter_EnvLinter_printWarning___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_printWarning___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_printWarning___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_printWarning___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_EnvLinter_printWarnings___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_printWarnings___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [45, 45, 32, 0]};
static mut l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_groupedByFilename___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [47, 45, 32, 84, 104, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 108, 105, 110, 116, 101, 114, 32, 114, 101, 112, 111, 114, 116, 115, 58, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 45, 47, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [47, 45, 32, 79, 75, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        45, 45, 32, 40, 110, 111, 110, 45, 100, 101, 102, 97, 117, 108, 116, 32, 108, 105, 110,
        116, 101, 114, 115, 32, 115, 107, 105, 112, 112, 101, 100, 41, 10, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value:
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
    m_data: [32, 105, 110, 32, 0],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value:
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
        32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 40, 112, 108, 117, 115,
        32, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 103, 101, 110, 101,
        114, 97, 116, 101, 100, 32, 111, 110, 101, 115, 41, 32, 0,
    ],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value:
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
    m_data: [32, 119, 105, 116, 104, 32, 0],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value:
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
    m_data: [32, 108, 105, 110, 116, 101, 114, 115, 10, 10, 0],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value:
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
    m_data: [45, 45, 32, 70, 111, 117, 110, 100, 32, 0],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value:
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
    m_data: [32, 101, 114, 114, 111, 114, 0],
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value:
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
static mut l_Lean_Linter_EnvLinter_formatLinterResults___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0_value:
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
    m_fun: l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(
    mut v_x_3513_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3513_ {
        0 => {
            let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3514_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3514_;
        }
        1 => {
            let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3515_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3515_;
        }
        _ => {
            let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3516_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3516_;
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx___boxed(
    mut v_x_3517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3518_: u8 = 0;
    let mut v_res_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3518_ = (crate::leanh::lean_unbox(v_x_3517_) as u8);
    v_res_3519_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_boxed_3518_);
    return v_res_3519_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(
    mut v_x_3520_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_3520_);
    return v___x_3521_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx___boxed(
    mut v_x_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3523_: u8 = 0;
    let mut v_res_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3523_ = (crate::leanh::lean_unbox(v_x_3522_) as u8);
    v_res_3524_ = l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(v_x_4__boxed_3523_);
    return v_res_3524_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(
    mut v_k_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3525_);
    return v_k_3525_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg___boxed(
    mut v_k_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(v_k_3526_);
    crate::leanh::lean_dec(v_k_3526_);
    return v_res_3527_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(
    mut v_motive_3528_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3529_: *mut crate::leanh::LeanObject,
    mut v_t_3530_: u8,
    mut v_h_3531_: *mut crate::leanh::LeanObject,
    mut v_k_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3532_);
    return v_k_3532_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___boxed(
    mut v_motive_3533_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3534_: *mut crate::leanh::LeanObject,
    mut v_t_3535_: *mut crate::leanh::LeanObject,
    mut v_h_3536_: *mut crate::leanh::LeanObject,
    mut v_k_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3538_: u8 = 0;
    let mut v_res_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3538_ = (crate::leanh::lean_unbox(v_t_3535_) as u8);
    v_res_3539_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(
        v_motive_3533_,
        v_ctorIdx_3534_,
        v_t_boxed_3538_,
        v_h_3536_,
        v_k_3537_,
    );
    crate::leanh::lean_dec(v_k_3537_);
    crate::leanh::lean_dec(v_ctorIdx_3534_);
    return v_res_3539_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(
    mut v_low_3540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_low_3540_);
    return v_low_3540_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg___boxed(
    mut v_low_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(v_low_3541_);
    crate::leanh::lean_dec(v_low_3541_);
    return v_res_3542_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(
    mut v_motive_3543_: *mut crate::leanh::LeanObject,
    mut v_t_3544_: u8,
    mut v_h_3545_: *mut crate::leanh::LeanObject,
    mut v_low_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_low_3546_);
    return v_low_3546_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___boxed(
    mut v_motive_3547_: *mut crate::leanh::LeanObject,
    mut v_t_3548_: *mut crate::leanh::LeanObject,
    mut v_h_3549_: *mut crate::leanh::LeanObject,
    mut v_low_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3551_: u8 = 0;
    let mut v_res_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3551_ = (crate::leanh::lean_unbox(v_t_3548_) as u8);
    v_res_3552_ = l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(
        v_motive_3547_,
        v_t_boxed_3551_,
        v_h_3549_,
        v_low_3550_,
    );
    crate::leanh::lean_dec(v_low_3550_);
    return v_res_3552_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(
    mut v_medium_3553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_medium_3553_);
    return v_medium_3553_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg___boxed(
    mut v_medium_3554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3555_ = l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(v_medium_3554_);
    crate::leanh::lean_dec(v_medium_3554_);
    return v_res_3555_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(
    mut v_motive_3556_: *mut crate::leanh::LeanObject,
    mut v_t_3557_: u8,
    mut v_h_3558_: *mut crate::leanh::LeanObject,
    mut v_medium_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_medium_3559_);
    return v_medium_3559_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___boxed(
    mut v_motive_3560_: *mut crate::leanh::LeanObject,
    mut v_t_3561_: *mut crate::leanh::LeanObject,
    mut v_h_3562_: *mut crate::leanh::LeanObject,
    mut v_medium_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3564_: u8 = 0;
    let mut v_res_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3564_ = (crate::leanh::lean_unbox(v_t_3561_) as u8);
    v_res_3565_ = l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(
        v_motive_3560_,
        v_t_boxed_3564_,
        v_h_3562_,
        v_medium_3563_,
    );
    crate::leanh::lean_dec(v_medium_3563_);
    return v_res_3565_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(
    mut v_high_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_high_3566_);
    return v_high_3566_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg___boxed(
    mut v_high_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ = l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(v_high_3567_);
    crate::leanh::lean_dec(v_high_3567_);
    return v_res_3568_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(
    mut v_motive_3569_: *mut crate::leanh::LeanObject,
    mut v_t_3570_: u8,
    mut v_h_3571_: *mut crate::leanh::LeanObject,
    mut v_high_3572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_high_3572_);
    return v_high_3572_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___boxed(
    mut v_motive_3573_: *mut crate::leanh::LeanObject,
    mut v_t_3574_: *mut crate::leanh::LeanObject,
    mut v_h_3575_: *mut crate::leanh::LeanObject,
    mut v_high_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3577_: u8 = 0;
    let mut v_res_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3577_ = (crate::leanh::lean_unbox(v_t_3574_) as u8);
    v_res_3578_ = l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(
        v_motive_3573_,
        v_t_boxed_3577_,
        v_h_3575_,
        v_high_3576_,
    );
    crate::leanh::lean_dec(v_high_3576_);
    return v_res_3578_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default() -> u8 {
    let mut v___x_3579_: u8 = 0;
    v___x_3579_ = 0;
    return v___x_3579_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity() -> u8 {
    let mut v___x_3580_: u8 = 0;
    v___x_3580_ = 0;
    return v___x_3580_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(
    mut v_n_3581_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: u8 = 0;
    v___x_3582_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3583_ = lean_nat_dec_le(v_n_3581_, v___x_3582_);
    if v___x_3583_ == 0 {
        let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3585_: u8 = 0;
        v___x_3584_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3585_ = lean_nat_dec_le(v_n_3581_, v___x_3584_);
        if v___x_3585_ == 0 {
            let mut v___x_3586_: u8 = 0;
            v___x_3586_ = 2;
            return v___x_3586_;
        } else {
            let mut v___x_3587_: u8 = 0;
            v___x_3587_ = 1;
            return v___x_3587_;
        }
    } else {
        let mut v___x_3588_: u8 = 0;
        v___x_3588_ = 0;
        return v___x_3588_;
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintVerbosity_ofNat___boxed(
    mut v_n_3589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3590_: u8 = 0;
    let mut v_r_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3590_ = l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(v_n_3589_);
    crate::leanh::lean_dec(v_n_3589_);
    v_r_3591_ = crate::leanh::lean_box((v_res_3590_) as usize);
    return v_r_3591_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(
    mut v_x_3592_: u8,
    mut v_y_3593_: u8,
) -> u8 {
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    v___x_3594_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_3592_);
    v___x_3595_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_y_3593_);
    v___x_3596_ = lean_nat_dec_eq(v___x_3594_, v___x_3595_);
    crate::leanh::lean_dec(v___x_3595_);
    crate::leanh::lean_dec(v___x_3594_);
    return v___x_3596_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity___boxed(
    mut v_x_3597_: *mut crate::leanh::LeanObject,
    mut v_y_3598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_3599_: u8 = 0;
    let mut v_y_14__boxed_3600_: u8 = 0;
    let mut v_res_3601_: u8 = 0;
    let mut v_r_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_3599_ = (crate::leanh::lean_unbox(v_x_3597_) as u8);
    v_y_14__boxed_3600_ = (crate::leanh::lean_unbox(v_y_3598_) as u8);
    v_res_3601_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(
        v_x_13__boxed_3599_,
        v_y_14__boxed_3600_,
    );
    v_r_3602_ = crate::leanh::lean_box((v_res_3601_) as usize);
    return v_r_3602_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3613_ = lean_nat_to_int(v___x_3612_);
    return v___x_3613_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3615_ = lean_nat_to_int(v___x_3614_);
    return v___x_3615_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(
    mut v_x_3616_: u8,
    mut v_prec_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: u8 = 0;
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match v_x_3616_ {
                    0 => {
                        v___x_3639_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3640_ = lean_nat_dec_le(v___x_3639_, v_prec_3617_);
                        if v___x_3640_ == 0 {
                            v___x_3641_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
                            v___y_3619_ = v___x_3641_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
                            v___y_3619_ = v___x_3642_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v___x_3643_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3644_ = lean_nat_dec_le(v___x_3643_, v_prec_3617_);
                        if v___x_3644_ == 0 {
                            v___x_3645_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
                            v___y_3626_ = v___x_3645_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3646_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
                            v___y_3626_ = v___x_3646_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3647_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3648_ = lean_nat_dec_le(v___x_3647_, v_prec_3617_);
                        if v___x_3648_ == 0 {
                            v___x_3649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
                            v___y_3633_ = v___x_3649_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3650_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
                            v___y_3633_ = v___x_3650_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3620_ = l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1;
                crate::leanh::lean_inc(v___y_3619_);
                v___x_3621_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3621_, 0, v___y_3619_);
                crate::leanh::lean_ctor_set(v___x_3621_, 1, v___x_3620_);
                v___x_3622_ = 0;
                v___x_3623_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3623_, 0, v___x_3621_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3623_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3622_,
                );
                v___x_3624_ = l_Repr_addAppParen(v___x_3623_, v_prec_3617_);
                return v___x_3624_;
            }
            2 => {
                v___x_3627_ = l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3;
                crate::leanh::lean_inc(v___y_3626_);
                v___x_3628_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3628_, 0, v___y_3626_);
                crate::leanh::lean_ctor_set(v___x_3628_, 1, v___x_3627_);
                v___x_3629_ = 0;
                v___x_3630_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3630_, 0, v___x_3628_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3629_,
                );
                v___x_3631_ = l_Repr_addAppParen(v___x_3630_, v_prec_3617_);
                return v___x_3631_;
            }
            3 => {
                v___x_3634_ = l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5;
                crate::leanh::lean_inc(v___y_3633_);
                v___x_3635_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3635_, 0, v___y_3633_);
                crate::leanh::lean_ctor_set(v___x_3635_, 1, v___x_3634_);
                v___x_3636_ = 0;
                v___x_3637_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3637_, 0, v___x_3635_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3637_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3636_,
                );
                v___x_3638_ = l_Repr_addAppParen(v___x_3637_, v_prec_3617_);
                return v___x_3638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed(
    mut v_x_3651_: *mut crate::leanh::LeanObject,
    mut v_prec_3652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_177__boxed_3653_: u8 = 0;
    let mut v_res_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_3653_ = (crate::leanh::lean_unbox(v_x_3651_) as u8);
    v_res_3654_ =
        l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(v_x_177__boxed_3653_, v_prec_3652_);
    crate::leanh::lean_dec(v_prec_3652_);
    return v_res_3654_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ctorIdx(
    mut v_x_3657_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3657_ {
        0 => {
            let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3658_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3658_;
        }
        1 => {
            let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3659_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3659_;
        }
        _ => {
            let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3660_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3660_;
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ctorIdx___boxed(
    mut v_x_3661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3662_: u8 = 0;
    let mut v_res_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3662_ = (crate::leanh::lean_unbox(v_x_3661_) as u8);
    v_res_3663_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_boxed_3662_);
    return v_res_3663_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(
    mut v_x_3664_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_3664_);
    return v___x_3665_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_toCtorIdx___boxed(
    mut v_x_3666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3667_: u8 = 0;
    let mut v_res_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3667_ = (crate::leanh::lean_unbox(v_x_3666_) as u8);
    v_res_3668_ = l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(v_x_4__boxed_3667_);
    return v_res_3668_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(
    mut v_k_3669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3669_);
    return v_k_3669_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg___boxed(
    mut v_k_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3671_ = l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(v_k_3670_);
    crate::leanh::lean_dec(v_k_3670_);
    return v_res_3671_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ctorElim(
    mut v_motive_3672_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3673_: *mut crate::leanh::LeanObject,
    mut v_t_3674_: u8,
    mut v_h_3675_: *mut crate::leanh::LeanObject,
    mut v_k_3676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3676_);
    return v_k_3676_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ctorElim___boxed(
    mut v_motive_3677_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3678_: *mut crate::leanh::LeanObject,
    mut v_t_3679_: *mut crate::leanh::LeanObject,
    mut v_h_3680_: *mut crate::leanh::LeanObject,
    mut v_k_3681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3682_: u8 = 0;
    let mut v_res_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3682_ = (crate::leanh::lean_unbox(v_t_3679_) as u8);
    v_res_3683_ = l_Lean_Linter_EnvLinter_LintScope_ctorElim(
        v_motive_3677_,
        v_ctorIdx_3678_,
        v_t_boxed_3682_,
        v_h_3680_,
        v_k_3681_,
    );
    crate::leanh::lean_dec(v_k_3681_);
    crate::leanh::lean_dec(v_ctorIdx_3678_);
    return v_res_3683_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(
    mut v_default_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_default_3684_);
    return v_default_3684_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg___boxed(
    mut v_default_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(v_default_3685_);
    crate::leanh::lean_dec(v_default_3685_);
    return v_res_3686_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_default_elim(
    mut v_motive_3687_: *mut crate::leanh::LeanObject,
    mut v_t_3688_: u8,
    mut v_h_3689_: *mut crate::leanh::LeanObject,
    mut v_default_3690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_default_3690_);
    return v_default_3690_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_default_elim___boxed(
    mut v_motive_3691_: *mut crate::leanh::LeanObject,
    mut v_t_3692_: *mut crate::leanh::LeanObject,
    mut v_h_3693_: *mut crate::leanh::LeanObject,
    mut v_default_3694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3695_: u8 = 0;
    let mut v_res_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3695_ = (crate::leanh::lean_unbox(v_t_3692_) as u8);
    v_res_3696_ = l_Lean_Linter_EnvLinter_LintScope_default_elim(
        v_motive_3691_,
        v_t_boxed_3695_,
        v_h_3693_,
        v_default_3694_,
    );
    crate::leanh::lean_dec(v_default_3694_);
    return v_res_3696_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg(
    mut v_extra_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_extra_3697_);
    return v_extra_3697_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg___boxed(
    mut v_extra_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3699_ = l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg(v_extra_3698_);
    crate::leanh::lean_dec(v_extra_3698_);
    return v_res_3699_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_extra_elim(
    mut v_motive_3700_: *mut crate::leanh::LeanObject,
    mut v_t_3701_: u8,
    mut v_h_3702_: *mut crate::leanh::LeanObject,
    mut v_extra_3703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_extra_3703_);
    return v_extra_3703_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_extra_elim___boxed(
    mut v_motive_3704_: *mut crate::leanh::LeanObject,
    mut v_t_3705_: *mut crate::leanh::LeanObject,
    mut v_h_3706_: *mut crate::leanh::LeanObject,
    mut v_extra_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3708_: u8 = 0;
    let mut v_res_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3708_ = (crate::leanh::lean_unbox(v_t_3705_) as u8);
    v_res_3709_ = l_Lean_Linter_EnvLinter_LintScope_extra_elim(
        v_motive_3704_,
        v_t_boxed_3708_,
        v_h_3706_,
        v_extra_3707_,
    );
    crate::leanh::lean_dec(v_extra_3707_);
    return v_res_3709_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(
    mut v_all_3710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_3710_);
    return v_all_3710_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg___boxed(
    mut v_all_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3712_ = l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(v_all_3711_);
    crate::leanh::lean_dec(v_all_3711_);
    return v_res_3712_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_all_elim(
    mut v_motive_3713_: *mut crate::leanh::LeanObject,
    mut v_t_3714_: u8,
    mut v_h_3715_: *mut crate::leanh::LeanObject,
    mut v_all_3716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_3716_);
    return v_all_3716_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_all_elim___boxed(
    mut v_motive_3717_: *mut crate::leanh::LeanObject,
    mut v_t_3718_: *mut crate::leanh::LeanObject,
    mut v_h_3719_: *mut crate::leanh::LeanObject,
    mut v_all_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3721_: u8 = 0;
    let mut v_res_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3721_ = (crate::leanh::lean_unbox(v_t_3718_) as u8);
    v_res_3722_ = l_Lean_Linter_EnvLinter_LintScope_all_elim(
        v_motive_3717_,
        v_t_boxed_3721_,
        v_h_3719_,
        v_all_3720_,
    );
    crate::leanh::lean_dec(v_all_3720_);
    return v_res_3722_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope_default() -> u8 {
    let mut v___x_3723_: u8 = 0;
    v___x_3723_ = 0;
    return v___x_3723_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope() -> u8 {
    let mut v___x_3724_: u8 = 0;
    v___x_3724_ = 0;
    return v___x_3724_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ofNat(
    mut v_n_3725_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: u8 = 0;
    v___x_3726_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3727_ = lean_nat_dec_le(v_n_3725_, v___x_3726_);
    if v___x_3727_ == 0 {
        let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3729_: u8 = 0;
        v___x_3728_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3729_ = lean_nat_dec_le(v_n_3725_, v___x_3728_);
        if v___x_3729_ == 0 {
            let mut v___x_3730_: u8 = 0;
            v___x_3730_ = 2;
            return v___x_3730_;
        } else {
            let mut v___x_3731_: u8 = 0;
            v___x_3731_ = 1;
            return v___x_3731_;
        }
    } else {
        let mut v___x_3732_: u8 = 0;
        v___x_3732_ = 0;
        return v___x_3732_;
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_LintScope_ofNat___boxed(
    mut v_n_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3734_: u8 = 0;
    let mut v_r_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3734_ = l_Lean_Linter_EnvLinter_LintScope_ofNat(v_n_3733_);
    crate::leanh::lean_dec(v_n_3733_);
    v_r_3735_ = crate::leanh::lean_box((v_res_3734_) as usize);
    return v_r_3735_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_instDecidableEqLintScope(
    mut v_x_3736_: u8,
    mut v_y_3737_: u8,
) -> u8 {
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    v___x_3738_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_3736_);
    v___x_3739_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_y_3737_);
    v___x_3740_ = lean_nat_dec_eq(v___x_3738_, v___x_3739_);
    crate::leanh::lean_dec(v___x_3739_);
    crate::leanh::lean_dec(v___x_3738_);
    return v___x_3740_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_instDecidableEqLintScope___boxed(
    mut v_x_3741_: *mut crate::leanh::LeanObject,
    mut v_y_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_3743_: u8 = 0;
    let mut v_y_14__boxed_3744_: u8 = 0;
    let mut v_res_3745_: u8 = 0;
    let mut v_r_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_3743_ = (crate::leanh::lean_unbox(v_x_3741_) as u8);
    v_y_14__boxed_3744_ = (crate::leanh::lean_unbox(v_y_3742_) as u8);
    v_res_3745_ =
        l_Lean_Linter_EnvLinter_instDecidableEqLintScope(v_x_13__boxed_3743_, v_y_14__boxed_3744_);
    v_r_3746_ = crate::leanh::lean_box((v_res_3745_) as usize);
    return v_r_3746_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_instReprLintScope_repr(
    mut v_x_3756_: u8,
    mut v_prec_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: u8 = 0;
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: u8 = 0;
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: u8 = 0;
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match v_x_3756_ {
                    0 => {
                        v___x_3779_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3780_ = lean_nat_dec_le(v___x_3779_, v_prec_3757_);
                        if v___x_3780_ == 0 {
                            v___x_3781_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
                            v___y_3759_ = v___x_3781_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3782_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
                            v___y_3759_ = v___x_3782_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v___x_3783_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3784_ = lean_nat_dec_le(v___x_3783_, v_prec_3757_);
                        if v___x_3784_ == 0 {
                            v___x_3785_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
                            v___y_3766_ = v___x_3785_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3786_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
                            v___y_3766_ = v___x_3786_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3787_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_3788_ = lean_nat_dec_le(v___x_3787_, v_prec_3757_);
                        if v___x_3788_ == 0 {
                            v___x_3789_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
                            v___y_3773_ = v___x_3789_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3790_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once), _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
                            v___y_3773_ = v___x_3790_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3760_ = l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1;
                crate::leanh::lean_inc(v___y_3759_);
                v___x_3761_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3761_, 0, v___y_3759_);
                crate::leanh::lean_ctor_set(v___x_3761_, 1, v___x_3760_);
                v___x_3762_ = 0;
                v___x_3763_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3761_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3763_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3762_,
                );
                v___x_3764_ = l_Repr_addAppParen(v___x_3763_, v_prec_3757_);
                return v___x_3764_;
            }
            2 => {
                v___x_3767_ = l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3;
                crate::leanh::lean_inc(v___y_3766_);
                v___x_3768_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3768_, 0, v___y_3766_);
                crate::leanh::lean_ctor_set(v___x_3768_, 1, v___x_3767_);
                v___x_3769_ = 0;
                v___x_3770_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3770_, 0, v___x_3768_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3770_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3769_,
                );
                v___x_3771_ = l_Repr_addAppParen(v___x_3770_, v_prec_3757_);
                return v___x_3771_;
            }
            3 => {
                v___x_3774_ = l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5;
                crate::leanh::lean_inc(v___y_3773_);
                v___x_3775_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3775_, 0, v___y_3773_);
                crate::leanh::lean_ctor_set(v___x_3775_, 1, v___x_3774_);
                v___x_3776_ = 0;
                v___x_3777_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3777_, 0, v___x_3775_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3777_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3776_,
                );
                v___x_3778_ = l_Repr_addAppParen(v___x_3777_, v_prec_3757_);
                return v___x_3778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed(
    mut v_x_3791_: *mut crate::leanh::LeanObject,
    mut v_prec_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_173__boxed_3793_: u8 = 0;
    let mut v_res_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_173__boxed_3793_ = (crate::leanh::lean_unbox(v_x_3791_) as u8);
    v_res_3794_ =
        l_Lean_Linter_EnvLinter_instReprLintScope_repr(v_x_173__boxed_3793_, v_prec_3792_);
    crate::leanh::lean_dec(v_prec_3792_);
    return v_res_3794_;
}
pub unsafe fn l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(
    mut v_x1_3797_: *mut crate::leanh::LeanObject,
    mut v_x2_3798_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    v_name_3799_ = crate::leanh::lean_ctor_get(v_x1_3797_, 1);
    v_name_3800_ = crate::leanh::lean_ctor_get(v_x2_3798_, 1);
    v___x_3801_ = l_Lean_Name_lt(v_name_3799_, v_name_3800_);
    return v___x_3801_;
}
pub unsafe fn l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0___boxed(
    mut v_x1_3802_: *mut crate::leanh::LeanObject,
    mut v_x2_3803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3804_: u8 = 0;
    let mut v_r_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3804_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(
        v_x1_3802_, v_x2_3803_,
    );
    crate::leanh::lean_dec_ref(v_x2_3803_);
    crate::leanh::lean_dec_ref(v_x1_3802_);
    v_r_3805_ = crate::leanh::lean_box((v_res_3804_) as usize);
    return v_r_3805_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(
    mut v_a_3806_: *mut crate::leanh::LeanObject,
    mut v_as_3807_: *mut crate::leanh::LeanObject,
    mut v_k_3808_: *mut crate::leanh::LeanObject,
    mut v_x_3809_: *mut crate::leanh::LeanObject,
    mut v_x_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_midVal_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: u8 = 0;
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3811_ = lean_nat_add(v_x_3809_, v_x_3810_);
                v___x_3812_ = crate::leanh::lean_unsigned_to_nat(1);
                v_mid_3813_ = lean_nat_shiftr(v___x_3811_, v___x_3812_);
                crate::leanh::lean_dec(v___x_3811_);
                v_midVal_3814_ = lean_array_fget_borrowed(v_as_3807_, v_mid_3813_);
                v___x_3815_ =
                    l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(
                        v_midVal_3814_,
                        v_k_3808_,
                    );
                if v___x_3815_ == 0 {
                    crate::leanh::lean_dec(v_x_3810_);
                    v___x_3816_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_3808_, v_midVal_3814_);
                    if v___x_3816_ == 0 {
                        crate::leanh::lean_dec(v_x_3809_);
                        v___x_3817_ = lean_array_get_size(v_as_3807_);
                        v___x_3818_ = lean_nat_dec_lt(v_mid_3813_, v___x_3817_);
                        if v___x_3818_ == 0 {
                            crate::leanh::lean_dec(v_mid_3813_);
                            crate::leanh::lean_dec_ref(v_a_3806_);
                            return v_as_3807_;
                        } else {
                            v___x_3819_ = crate::leanh::lean_box(0);
                            v_xs_x27_3820_ = lean_array_fset(v_as_3807_, v_mid_3813_, v___x_3819_);
                            v___x_3821_ = lean_array_fset(v_xs_x27_3820_, v_mid_3813_, v_a_3806_);
                            crate::leanh::lean_dec(v_mid_3813_);
                            return v___x_3821_;
                        }
                    } else {
                        v_x_3810_ = v_mid_3813_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_3823_ = lean_nat_dec_eq(v_mid_3813_, v_x_3809_);
                    if v___x_3823_ == 0 {
                        crate::leanh::lean_dec(v_x_3809_);
                        v_x_3809_ = v_mid_3813_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_mid_3813_);
                        crate::leanh::lean_dec(v_x_3810_);
                        v___x_3825_ = lean_nat_add(v_x_3809_, v___x_3812_);
                        crate::leanh::lean_dec(v_x_3809_);
                        v_j_3826_ = lean_array_get_size(v_as_3807_);
                        v_as_3827_ = lean_array_push(v_as_3807_, v_a_3806_);
                        v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            crate::leanh::lean_box(0),
                            v___x_3825_,
                            v_as_3827_,
                            v_j_3826_,
                        );
                        crate::leanh::lean_dec(v___x_3825_);
                        return v___x_3828_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg___boxed(
    mut v_a_3829_: *mut crate::leanh::LeanObject,
    mut v_as_3830_: *mut crate::leanh::LeanObject,
    mut v_k_3831_: *mut crate::leanh::LeanObject,
    mut v_x_3832_: *mut crate::leanh::LeanObject,
    mut v_x_3833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3834_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_3829_, v_as_3830_, v_k_3831_, v_x_3832_, v_x_3833_);
    crate::leanh::lean_dec_ref(v_k_3831_);
    return v_res_3834_;
}
pub unsafe fn l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(
    mut v_a_3835_: *mut crate::leanh::LeanObject,
    mut v_as_3836_: *mut crate::leanh::LeanObject,
    mut v_k_3837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: u8 = 0;
    v___x_3838_ = lean_array_get_size(v_as_3836_);
    v___x_3839_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3840_ = lean_nat_dec_eq(v___x_3838_, v___x_3839_);
    if v___x_3840_ == 0 {
        let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3842_: u8 = 0;
        v___x_3841_ = lean_array_fget_borrowed(v_as_3836_, v___x_3839_);
        v___x_3842_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(
            v_k_3837_,
            v___x_3841_,
        );
        if v___x_3842_ == 0 {
            let mut v___x_3843_: u8 = 0;
            v___x_3843_ =
                l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(
                    v___x_3841_,
                    v_k_3837_,
                );
            if v___x_3843_ == 0 {
                let mut v___x_3844_: u8 = 0;
                v___x_3844_ = lean_nat_dec_lt(v___x_3839_, v___x_3838_);
                if v___x_3844_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_3835_);
                    return v_as_3836_;
                } else {
                    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3845_ = crate::leanh::lean_box(0);
                    v_xs_x27_3846_ = lean_array_fset(v_as_3836_, v___x_3839_, v___x_3845_);
                    v___x_3847_ = lean_array_fset(v_xs_x27_3846_, v___x_3839_, v_a_3835_);
                    return v___x_3847_;
                }
            } else {
                let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3851_: u8 = 0;
                v___x_3848_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3849_ = lean_nat_sub(v___x_3838_, v___x_3848_);
                v___x_3850_ = lean_array_fget_borrowed(v_as_3836_, v___x_3849_);
                v___x_3851_ =
                    l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(
                        v___x_3850_,
                        v_k_3837_,
                    );
                if v___x_3851_ == 0 {
                    let mut v___x_3852_: u8 = 0;
                    v___x_3852_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_3837_, v___x_3850_);
                    if v___x_3852_ == 0 {
                        let mut v___x_3853_: u8 = 0;
                        v___x_3853_ = lean_nat_dec_lt(v___x_3849_, v___x_3838_);
                        if v___x_3853_ == 0 {
                            crate::leanh::lean_dec(v___x_3849_);
                            crate::leanh::lean_dec_ref(v_a_3835_);
                            return v_as_3836_;
                        } else {
                            let mut v___x_3854_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_x27_3855_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3856_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_3854_ = crate::leanh::lean_box(0);
                            v_xs_x27_3855_ = lean_array_fset(v_as_3836_, v___x_3849_, v___x_3854_);
                            v___x_3856_ = lean_array_fset(v_xs_x27_3855_, v___x_3849_, v_a_3835_);
                            crate::leanh::lean_dec(v___x_3849_);
                            return v___x_3856_;
                        }
                    } else {
                        let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_3857_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_3835_, v_as_3836_, v_k_3837_, v___x_3839_, v___x_3849_);
                        return v___x_3857_;
                    }
                } else {
                    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_3849_);
                    v___x_3858_ = lean_array_push(v_as_3836_, v_a_3835_);
                    return v___x_3858_;
                }
            }
        } else {
            let mut v_as_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_as_3859_ = lean_array_push(v_as_3836_, v_a_3835_);
            v___x_3860_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                crate::leanh::lean_box(0),
                v___x_3839_,
                v_as_3859_,
                v___x_3838_,
            );
            return v___x_3860_;
        }
    } else {
        let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3861_ = lean_array_push(v_as_3836_, v_a_3835_);
        return v___x_3861_;
    }
}
pub unsafe fn l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___boxed(
    mut v_a_3862_: *mut crate::leanh::LeanObject,
    mut v_as_3863_: *mut crate::leanh::LeanObject,
    mut v_k_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3865_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(
        v_a_3862_, v_as_3863_, v_k_3864_,
    );
    crate::leanh::lean_dec_ref(v_k_3864_);
    return v_res_3865_;
}
pub unsafe fn l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(
    mut v_a_3866_: *mut crate::leanh::LeanObject,
    mut v_x_3867_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3868_: u8 = 0;
    let mut v_head_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3867_) == 0 {
                    v___x_3868_ = 0;
                    return v___x_3868_;
                } else {
                    v_head_3869_ = crate::leanh::lean_ctor_get(v_x_3867_, 0);
                    v_tail_3870_ = crate::leanh::lean_ctor_get(v_x_3867_, 1);
                    v___x_3871_ = lean_name_eq(v_a_3866_, v_head_3869_);
                    if v___x_3871_ == 0 {
                        v_x_3867_ = v_tail_3870_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3871_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1___boxed(
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_x_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3875_: u8 = 0;
    let mut v_r_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3875_ =
        l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(v_a_3873_, v_x_3874_);
    crate::leanh::lean_dec(v_x_3874_);
    crate::leanh::lean_dec(v_a_3873_);
    v_r_3876_ = crate::leanh::lean_box((v_res_3875_) as usize);
    return v_r_3876_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(
    mut v_runOnly_3877_: *mut crate::leanh::LeanObject,
    mut v_scope_3878_: u8,
    mut v_init_3879_: *mut crate::leanh::LeanObject,
    mut v_x_3880_: *mut crate::leanh::LeanObject,
    mut v___y_3881_: *mut crate::leanh::LeanObject,
    mut v___y_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v___y_3912_: u8 = 0;
    let mut v_a_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v_val_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: u8 = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3880_) == 0 {
                    v_k_3888_ = crate::leanh::lean_ctor_get(v_x_3880_, 1);
                    crate::leanh::lean_inc(v_k_3888_);
                    v_v_3889_ = crate::leanh::lean_ctor_get(v_x_3880_, 2);
                    crate::leanh::lean_inc(v_v_3889_);
                    v_l_3890_ = crate::leanh::lean_ctor_get(v_x_3880_, 3);
                    crate::leanh::lean_inc(v_l_3890_);
                    v_r_3891_ = crate::leanh::lean_ctor_get(v_x_3880_, 4);
                    crate::leanh::lean_inc(v_r_3891_);
                    crate::leanh::lean_dec_ref_known(v_x_3880_, 5);
                    v___x_3892_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_3877_, v_scope_3878_, v_init_3879_, v_l_3890_, v___y_3881_, v___y_3882_);
                    if crate::leanh::lean_obj_tag(v___x_3892_) == 0 {
                        v_a_3893_ = crate::leanh::lean_ctor_get(v___x_3892_, 0);
                        crate::leanh::lean_inc(v_a_3893_);
                        if crate::leanh::lean_obj_tag(v_a_3893_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3892_, 1);
                            crate::leanh::lean_dec(v_r_3891_);
                            crate::leanh::lean_dec(v_v_3889_);
                            crate::leanh::lean_dec(v_k_3888_);
                            v_a_3894_ = crate::leanh::lean_ctor_get(v_a_3893_, 0);
                            crate::leanh::lean_inc(v_a_3894_);
                            crate::leanh::lean_dec_ref_known(v_a_3893_, 1);
                            v_d_3885_ = v_a_3894_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3895_ = crate::leanh::lean_ctor_get(v_a_3893_, 0);
                            crate::leanh::lean_inc(v_a_3895_);
                            crate::leanh::lean_dec_ref_known(v_a_3893_, 1);
                            v_fst_3896_ = crate::leanh::lean_ctor_get(v_v_3889_, 0);
                            crate::leanh::lean_inc(v_fst_3896_);
                            v_snd_3897_ = crate::leanh::lean_ctor_get(v_v_3889_, 1);
                            crate::leanh::lean_inc(v_snd_3897_);
                            crate::leanh::lean_dec(v_v_3889_);
                            if crate::leanh::lean_obj_tag(v_runOnly_3877_) == 0 {
                                if v_scope_3878_ == 0 {
                                    v___x_3917_ = (crate::leanh::lean_unbox(v_snd_3897_) as u8);
                                    crate::leanh::lean_dec(v_snd_3897_);
                                    v___y_3912_ = v___x_3917_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_snd_3897_);
                                    crate::leanh::lean_dec_ref_known(v___x_3892_, 1);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_3897_);
                                v_val_3918_ = crate::leanh::lean_ctor_get(v_runOnly_3877_, 0);
                                v___x_3919_ =
                                    l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(
                                        v_k_3888_,
                                        v_val_3918_,
                                    );
                                v___y_3912_ = v___x_3919_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_3891_);
                        crate::leanh::lean_dec(v_v_3889_);
                        crate::leanh::lean_dec(v_k_3888_);
                        return v___x_3892_;
                    }
                } else {
                    v___x_3920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3920_, 0, v_init_3879_);
                    v___x_3921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3921_, 0, v___x_3920_);
                    return v___x_3921_;
                }
            }
            1 => {
                v___x_3886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3886_, 0, v_d_3885_);
                v___x_3887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3887_, 0, v___x_3886_);
                return v___x_3887_;
            }
            2 => {
                v___x_3899_ = l_Lean_Linter_EnvLinter_getEnvLinter(
                    v_k_3888_,
                    v_fst_3896_,
                    v___y_3881_,
                    v___y_3882_,
                );
                if crate::leanh::lean_obj_tag(v___x_3899_) == 0 {
                    v_a_3900_ = crate::leanh::lean_ctor_get(v___x_3899_, 0);
                    crate::leanh::lean_inc_n(v_a_3900_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3899_, 1);
                    v___x_3901_ =
                        l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(
                            v_a_3900_, v_a_3895_, v_a_3900_,
                        );
                    crate::leanh::lean_dec(v_a_3900_);
                    v_init_3879_ = v___x_3901_;
                    v_x_3880_ = v_r_3891_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3895_);
                    crate::leanh::lean_dec(v_r_3891_);
                    v_a_3903_ = crate::leanh::lean_ctor_get(v___x_3899_, 0);
                    v_isSharedCheck_3910_ = (!crate::leanh::lean_is_exclusive(v___x_3899_)) as u8;
                    if v_isSharedCheck_3910_ == 0 {
                        v___x_3905_ = v___x_3899_;
                        v_isShared_3906_ = v_isSharedCheck_3910_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3903_);
                        crate::leanh::lean_dec(v___x_3899_);
                        v___x_3905_ = crate::leanh::lean_box(0);
                        v_isShared_3906_ = v_isSharedCheck_3910_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3906_ == 0 {
                    v___x_3908_ = v___x_3905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3909_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3908_;
            }
            5 => {
                if v___y_3912_ == 0 {
                    crate::leanh::lean_dec(v_fst_3896_);
                    crate::leanh::lean_dec(v_a_3895_);
                    crate::leanh::lean_dec(v_k_3888_);
                    if crate::leanh::lean_obj_tag(v___x_3892_) == 0 {
                        v_a_3913_ = crate::leanh::lean_ctor_get(v___x_3892_, 0);
                        crate::leanh::lean_inc(v_a_3913_);
                        crate::leanh::lean_dec_ref_known(v___x_3892_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3913_) == 0 {
                            crate::leanh::lean_dec(v_r_3891_);
                            v_a_3914_ = crate::leanh::lean_ctor_get(v_a_3913_, 0);
                            crate::leanh::lean_inc(v_a_3914_);
                            crate::leanh::lean_dec_ref_known(v_a_3913_, 1);
                            v_d_3885_ = v_a_3914_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3915_ = crate::leanh::lean_ctor_get(v_a_3913_, 0);
                            crate::leanh::lean_inc(v_a_3915_);
                            crate::leanh::lean_dec_ref_known(v_a_3913_, 1);
                            v_init_3879_ = v_a_3915_;
                            v_x_3880_ = v_r_3891_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_3891_);
                        return v___x_3892_;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3892_, 1);
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2___boxed(
    mut v_runOnly_3922_: *mut crate::leanh::LeanObject,
    mut v_scope_3923_: *mut crate::leanh::LeanObject,
    mut v_init_3924_: *mut crate::leanh::LeanObject,
    mut v_x_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_scope_boxed_3929_: u8 = 0;
    let mut v_res_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_scope_boxed_3929_ = (crate::leanh::lean_unbox(v_scope_3923_) as u8);
    v_res_3930_ =
        l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(
            v_runOnly_3922_,
            v_scope_boxed_3929_,
            v_init_3924_,
            v_x_3925_,
            v___y_3926_,
            v___y_3927_,
        );
    crate::leanh::lean_dec(v___y_3927_);
    crate::leanh::lean_dec_ref(v___y_3926_);
    crate::leanh::lean_dec(v_runOnly_3922_);
    return v_res_3930_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getChecks(
    mut v_scope_3933_: u8,
    mut v_runOnly_3934_: *mut crate::leanh::LeanObject,
    mut v_a_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v_a_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3956_: u8 = 0;
    let mut v_a_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3960_: u8 = 0;
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3938_ = lean_st_ref_get(v_a_3936_);
                v_env_3939_ = crate::leanh::lean_ctor_get(v___x_3938_, 0);
                crate::leanh::lean_inc_ref(v_env_3939_);
                crate::leanh::lean_dec(v___x_3938_);
                v___x_3940_ = l_Lean_Linter_EnvLinter_envLinterExt;
                v_toEnvExtension_3941_ = crate::leanh::lean_ctor_get(v___x_3940_, 0);
                v_asyncMode_3942_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3941_, 2);
                v___x_3943_ = crate::leanh::lean_box(1);
                v_result_3944_ = l_Lean_Linter_EnvLinter_getChecks___closed__0;
                v___x_3945_ = crate::leanh::lean_box(0);
                v___x_3946_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3943_,
                    v___x_3940_,
                    v_env_3939_,
                    v_asyncMode_3942_,
                    v___x_3945_,
                );
                v___x_3947_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_3934_, v_scope_3933_, v_result_3944_, v___x_3946_, v_a_3935_, v_a_3936_);
                if crate::leanh::lean_obj_tag(v___x_3947_) == 0 {
                    v_a_3948_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                    v_isSharedCheck_3956_ = (!crate::leanh::lean_is_exclusive(v___x_3947_)) as u8;
                    if v_isSharedCheck_3956_ == 0 {
                        v___x_3950_ = v___x_3947_;
                        v_isShared_3951_ = v_isSharedCheck_3956_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3948_);
                        crate::leanh::lean_dec(v___x_3947_);
                        v___x_3950_ = crate::leanh::lean_box(0);
                        v_isShared_3951_ = v_isSharedCheck_3956_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3957_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                    v_isSharedCheck_3964_ = (!crate::leanh::lean_is_exclusive(v___x_3947_)) as u8;
                    if v_isSharedCheck_3964_ == 0 {
                        v___x_3959_ = v___x_3947_;
                        v_isShared_3960_ = v_isSharedCheck_3964_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3957_);
                        crate::leanh::lean_dec(v___x_3947_);
                        v___x_3959_ = crate::leanh::lean_box(0);
                        v_isShared_3960_ = v_isSharedCheck_3964_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3952_ = crate::leanh::lean_ctor_get(v_a_3948_, 0);
                crate::leanh::lean_inc(v_a_3952_);
                crate::leanh::lean_dec(v_a_3948_);
                if v_isShared_3951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3950_, 0, v_a_3952_);
                    v___x_3954_ = v___x_3950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3955_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3952_);
                    v___x_3954_ = v_reuseFailAlloc_3955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3954_;
            }
            3 => {
                if v_isShared_3960_ == 0 {
                    v___x_3962_ = v___x_3959_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3963_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
                    v___x_3962_ = v_reuseFailAlloc_3963_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_getChecks___boxed(
    mut v_scope_3965_: *mut crate::leanh::LeanObject,
    mut v_runOnly_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_a_3968_: *mut crate::leanh::LeanObject,
    mut v_a_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_scope_boxed_3970_: u8 = 0;
    let mut v_res_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_scope_boxed_3970_ = (crate::leanh::lean_unbox(v_scope_3965_) as u8);
    v_res_3971_ = l_Lean_Linter_EnvLinter_getChecks(
        v_scope_boxed_3970_,
        v_runOnly_3966_,
        v_a_3967_,
        v_a_3968_,
    );
    crate::leanh::lean_dec(v_a_3968_);
    crate::leanh::lean_dec_ref(v_a_3967_);
    crate::leanh::lean_dec(v_runOnly_3966_);
    return v_res_3971_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(
    mut v_a_3972_: *mut crate::leanh::LeanObject,
    mut v_as_3973_: *mut crate::leanh::LeanObject,
    mut v_k_3974_: *mut crate::leanh::LeanObject,
    mut v_x_3975_: *mut crate::leanh::LeanObject,
    mut v_x_3976_: *mut crate::leanh::LeanObject,
    mut v_x_3977_: *mut crate::leanh::LeanObject,
    mut v_x_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3979_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_3972_, v_as_3973_, v_k_3974_, v_x_3975_, v_x_3976_);
    return v___x_3979_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___boxed(
    mut v_a_3980_: *mut crate::leanh::LeanObject,
    mut v_as_3981_: *mut crate::leanh::LeanObject,
    mut v_k_3982_: *mut crate::leanh::LeanObject,
    mut v_x_3983_: *mut crate::leanh::LeanObject,
    mut v_x_3984_: *mut crate::leanh::LeanObject,
    mut v_x_3985_: *mut crate::leanh::LeanObject,
    mut v_x_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(v_a_3980_, v_as_3981_, v_k_3982_, v_x_3983_, v_x_3984_, v_x_3985_, v_x_3986_);
    crate::leanh::lean_dec_ref(v_k_3982_);
    return v_res_3987_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(
    mut v_a_3988_: *mut crate::leanh::LeanObject,
    mut v_as_3989_: *mut crate::leanh::LeanObject,
    mut v_i_3990_: usize,
    mut v_stop_3991_: usize,
) -> u8 {
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: u8 = 0;
    let mut v___x_3995_: usize = 0;
    let mut v___x_3996_: usize = 0;
    let mut v___x_3998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3992_ = lean_usize_dec_eq(v_i_3990_, v_stop_3991_);
                if v___x_3992_ == 0 {
                    v___x_3993_ = lean_array_uget_borrowed(v_as_3989_, v_i_3990_);
                    v___x_3994_ = lean_name_eq(v_a_3988_, v___x_3993_);
                    if v___x_3994_ == 0 {
                        v___x_3995_ = 1usize;
                        v___x_3996_ = lean_usize_add(v_i_3990_, v___x_3995_);
                        v_i_3990_ = v___x_3996_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3994_;
                    }
                } else {
                    v___x_3998_ = 0;
                    return v___x_3998_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8___boxed(
    mut v_a_3999_: *mut crate::leanh::LeanObject,
    mut v_as_4000_: *mut crate::leanh::LeanObject,
    mut v_i_4001_: *mut crate::leanh::LeanObject,
    mut v_stop_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4003_: usize = 0;
    let mut v_stop_boxed_4004_: usize = 0;
    let mut v_res_4005_: u8 = 0;
    let mut v_r_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4003_ = crate::leanh::lean_unbox_usize(v_i_4001_);
    crate::leanh::lean_dec(v_i_4001_);
    v_stop_boxed_4004_ = crate::leanh::lean_unbox_usize(v_stop_4002_);
    crate::leanh::lean_dec(v_stop_4002_);
    v_res_4005_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_3999_, v_as_4000_, v_i_boxed_4003_, v_stop_boxed_4004_);
    crate::leanh::lean_dec_ref(v_as_4000_);
    crate::leanh::lean_dec(v_a_3999_);
    v_r_4006_ = crate::leanh::lean_box((v_res_4005_) as usize);
    return v_r_4006_;
}
pub unsafe fn l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(
    mut v_as_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: u8 = 0;
    v___x_4009_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4010_ = lean_array_get_size(v_as_4007_);
    v___x_4011_ = lean_nat_dec_lt(v___x_4009_, v___x_4010_);
    if v___x_4011_ == 0 {
        return v___x_4011_;
    } else {
        if v___x_4011_ == 0 {
            return v___x_4011_;
        } else {
            let mut v___x_4012_: usize = 0;
            let mut v___x_4013_: usize = 0;
            let mut v___x_4014_: u8 = 0;
            v___x_4012_ = 0usize;
            v___x_4013_ = lean_usize_of_nat(v___x_4010_);
            v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_4008_, v_as_4007_, v___x_4012_, v___x_4013_);
            return v___x_4014_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6___boxed(
    mut v_as_4015_: *mut crate::leanh::LeanObject,
    mut v_a_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4017_: u8 = 0;
    let mut v_r_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v_as_4015_, v_a_4016_);
    crate::leanh::lean_dec(v_a_4016_);
    crate::leanh::lean_dec_ref(v_as_4015_);
    v_r_4018_ = crate::leanh::lean_box((v_res_4017_) as usize);
    return v_r_4018_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4019_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_4019_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(
    mut v_linter_4022_: *mut crate::leanh::LeanObject,
    mut v_decl_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4026_ = lean_st_ref_get(v___y_4024_);
                v_env_4036_ = crate::leanh::lean_ctor_get(v___x_4026_, 0);
                crate::leanh::lean_inc_ref(v_env_4036_);
                crate::leanh::lean_dec(v___x_4026_);
                v___x_4037_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0_once), _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0);
                v___x_4038_ = l_Lean_Linter_EnvLinter_builtinNolintAttr;
                v___x_4039_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                    v___x_4037_,
                    v___x_4038_,
                    v_env_4036_,
                    v_decl_4023_,
                );
                if crate::leanh::lean_obj_tag(v___x_4039_) == 0 {
                    v___x_4040_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1;
                    v___y_4028_ = v___x_4040_;
                    state = 1;
                    continue;
                } else {
                    v_val_4041_ = crate::leanh::lean_ctor_get(v___x_4039_, 0);
                    crate::leanh::lean_inc(v_val_4041_);
                    crate::leanh::lean_dec_ref_known(v___x_4039_, 1);
                    v___y_4028_ = v_val_4041_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4029_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v___y_4028_, v_linter_4022_);
                crate::leanh::lean_dec_ref(v___y_4028_);
                if v___x_4029_ == 0 {
                    v___x_4030_ = 1;
                    v___x_4031_ = crate::leanh::lean_box((v___x_4030_) as usize);
                    v___x_4032_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4032_, 0, v___x_4031_);
                    return v___x_4032_;
                } else {
                    v___x_4033_ = 0;
                    v___x_4034_ = crate::leanh::lean_box((v___x_4033_) as usize);
                    v___x_4035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4035_, 0, v___x_4034_);
                    return v___x_4035_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___boxed(
    mut v_linter_4042_: *mut crate::leanh::LeanObject,
    mut v_decl_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_4042_, v_decl_4043_, v___y_4044_);
    crate::leanh::lean_dec(v___y_4044_);
    crate::leanh::lean_dec(v_linter_4042_);
    return v_res_4046_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(
    mut v___x_4047_: *mut crate::leanh::LeanObject,
    mut v_as_4048_: *mut crate::leanh::LeanObject,
    mut v_i_4049_: usize,
    mut v_stop_4050_: usize,
    mut v_b_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: usize = 0;
    let mut v___x_4062_: usize = 0;
    let mut v___x_4064_: u8 = 0;
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4073_: u8 = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4055_ = lean_usize_dec_eq(v_i_4049_, v_stop_4050_);
                if v___x_4055_ == 0 {
                    v___x_4056_ = lean_array_uget_borrowed(v_as_4048_, v_i_4049_);
                    crate::leanh::lean_inc(v___x_4056_);
                    v___x_4057_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v___x_4047_, v___x_4056_, v___y_4053_);
                    if crate::leanh::lean_obj_tag(v___x_4057_) == 0 {
                        v_a_4058_ = crate::leanh::lean_ctor_get(v___x_4057_, 0);
                        crate::leanh::lean_inc(v_a_4058_);
                        crate::leanh::lean_dec_ref_known(v___x_4057_, 1);
                        v___x_4064_ = (crate::leanh::lean_unbox(v_a_4058_) as u8);
                        crate::leanh::lean_dec(v_a_4058_);
                        if v___x_4064_ == 0 {
                            v_a_4060_ = v_b_4051_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_4056_);
                            v___x_4065_ = lean_array_push(v_b_4051_, v___x_4056_);
                            v_a_4060_ = v___x_4065_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4051_);
                        v_a_4066_ = crate::leanh::lean_ctor_get(v___x_4057_, 0);
                        v_isSharedCheck_4073_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4057_)) as u8;
                        if v_isSharedCheck_4073_ == 0 {
                            v___x_4068_ = v___x_4057_;
                            v_isShared_4069_ = v_isSharedCheck_4073_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4066_);
                            crate::leanh::lean_dec(v___x_4057_);
                            v___x_4068_ = crate::leanh::lean_box(0);
                            v_isShared_4069_ = v_isSharedCheck_4073_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_4074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4074_, 0, v_b_4051_);
                    return v___x_4074_;
                }
            }
            1 => {
                v___x_4061_ = 1usize;
                v___x_4062_ = lean_usize_add(v_i_4049_, v___x_4061_);
                v_i_4049_ = v___x_4062_;
                v_b_4051_ = v_a_4060_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4069_ == 0 {
                    v___x_4071_ = v___x_4068_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
                    v___x_4071_ = v_reuseFailAlloc_4072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(
    mut v___x_4075_: *mut crate::leanh::LeanObject,
    mut v_as_4076_: *mut crate::leanh::LeanObject,
    mut v_i_4077_: *mut crate::leanh::LeanObject,
    mut v_stop_4078_: *mut crate::leanh::LeanObject,
    mut v_b_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
    mut v___y_4082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4083_: usize = 0;
    let mut v_stop_boxed_4084_: usize = 0;
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4083_ = crate::leanh::lean_unbox_usize(v_i_4077_);
    crate::leanh::lean_dec(v_i_4077_);
    v_stop_boxed_4084_ = crate::leanh::lean_unbox_usize(v_stop_4078_);
    crate::leanh::lean_dec(v_stop_4078_);
    v_res_4085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v___x_4075_, v_as_4076_, v_i_boxed_4083_, v_stop_boxed_4084_, v_b_4079_, v___y_4080_, v___y_4081_);
    crate::leanh::lean_dec(v___y_4081_);
    crate::leanh::lean_dec_ref(v___y_4080_);
    crate::leanh::lean_dec_ref(v_as_4076_);
    crate::leanh::lean_dec(v___x_4075_);
    return v_res_4085_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4086_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4087_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0);
    v___x_4088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4088_, 0, v___x_4087_);
    return v___x_4088_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
    v___x_4090_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4090_, 0, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4090_, 1, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4090_, 2, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4090_, 3, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4090_, 4, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4090_, 5, v___x_4089_);
    return v___x_4090_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4091_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4092_ = lean_mk_empty_array_with_capacity(v___x_4091_);
    v___x_4093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
    return v___x_4093_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4094_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
    v___x_4095_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4095_, 0, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 1, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 2, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 3, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 4, v___x_4094_);
    return v___x_4095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(
    mut v___x_4096_: *mut crate::leanh::LeanObject,
    mut v___x_4097_: *mut crate::leanh::LeanObject,
    mut v_test_4098_: *mut crate::leanh::LeanObject,
    mut v_v_4099_: *mut crate::leanh::LeanObject,
    mut v_x_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: usize = 0;
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4104_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
                crate::leanh::lean_inc_n(v___x_4096_, 5);
                v___x_4105_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4105_, 0, v___x_4096_);
                crate::leanh::lean_ctor_set(v___x_4105_, 1, v___x_4096_);
                crate::leanh::lean_ctor_set(v___x_4105_, 2, v___x_4096_);
                crate::leanh::lean_ctor_set(v___x_4105_, 3, v___x_4096_);
                crate::leanh::lean_ctor_set(v___x_4105_, 4, v___x_4104_);
                crate::leanh::lean_ctor_set(v___x_4105_, 5, v___x_4104_);
                crate::leanh::lean_ctor_set(v___x_4105_, 6, v___x_4104_);
                crate::leanh::lean_ctor_set(v___x_4105_, 7, v___x_4104_);
                crate::leanh::lean_ctor_set(v___x_4105_, 8, v___x_4104_);
                crate::leanh::lean_ctor_set(v___x_4105_, 9, v___x_4104_);
                v___x_4106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2);
                v___x_4107_ = crate::leanh::lean_unsigned_to_nat(32);
                v___x_4108_ = lean_mk_empty_array_with_capacity(v___x_4107_);
                v___x_4109_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3);
                v___x_4110_ = 5usize;
                v___x_4111_ =
                    crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4109_);
                crate::leanh::lean_ctor_set(v___x_4111_, 1, v___x_4108_);
                crate::leanh::lean_ctor_set(v___x_4111_, 2, v___x_4096_);
                crate::leanh::lean_ctor_set(v___x_4111_, 3, v___x_4096_);
                crate::leanh::lean_ctor_set_usize(v___x_4111_, 4, v___x_4110_);
                v___x_4112_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4);
                v___x_4113_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4113_, 0, v___x_4105_);
                crate::leanh::lean_ctor_set(v___x_4113_, 1, v___x_4106_);
                crate::leanh::lean_ctor_set(v___x_4113_, 2, v___x_4097_);
                crate::leanh::lean_ctor_set(v___x_4113_, 3, v___x_4111_);
                crate::leanh::lean_ctor_set(v___x_4113_, 4, v___x_4112_);
                v___x_4114_ = lean_st_mk_ref(v___x_4113_);
                v___x_4115_ = l_Lean_Elab_Command_mkMetaContext;
                crate::leanh::lean_inc(v___y_4102_);
                crate::leanh::lean_inc_ref(v___y_4101_);
                crate::leanh::lean_inc(v___x_4114_);
                v___x_4116_ = crate::leanh::lean_apply_6(
                    v_test_4098_,
                    v_v_4099_,
                    v___x_4115_,
                    v___x_4114_,
                    v___y_4101_,
                    v___y_4102_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4116_) == 0 {
                    v_a_4117_ = crate::leanh::lean_ctor_get(v___x_4116_, 0);
                    v_isSharedCheck_4125_ = (!crate::leanh::lean_is_exclusive(v___x_4116_)) as u8;
                    if v_isSharedCheck_4125_ == 0 {
                        v___x_4119_ = v___x_4116_;
                        v_isShared_4120_ = v_isSharedCheck_4125_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4117_);
                        crate::leanh::lean_dec(v___x_4116_);
                        v___x_4119_ = crate::leanh::lean_box(0);
                        v_isShared_4120_ = v_isSharedCheck_4125_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4114_);
                    return v___x_4116_;
                }
            }
            1 => {
                v___x_4121_ = lean_st_ref_get(v___x_4114_);
                crate::leanh::lean_dec(v___x_4114_);
                crate::leanh::lean_dec(v___x_4121_);
                if v_isShared_4120_ == 0 {
                    v___x_4123_ = v___x_4119_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4117_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(
    mut v___x_4126_: *mut crate::leanh::LeanObject,
    mut v___x_4127_: *mut crate::leanh::LeanObject,
    mut v_test_4128_: *mut crate::leanh::LeanObject,
    mut v_v_4129_: *mut crate::leanh::LeanObject,
    mut v_x_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(v___x_4126_, v___x_4127_, v_test_4128_, v_v_4129_, v_x_4130_, v___y_4131_, v___y_4132_);
    crate::leanh::lean_dec(v___y_4132_);
    crate::leanh::lean_dec_ref(v___y_4131_);
    return v_res_4134_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(
    mut v_a_4135_: *mut crate::leanh::LeanObject,
    mut v___x_4136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4146_: u8 = 0;
    let mut v_a_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4150_: u8 = 0;
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4138_ =
                    crate::leanh::lean_apply_2(v_a_4135_, v___x_4136_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_4138_) == 0 {
                    v_a_4139_ = crate::leanh::lean_ctor_get(v___x_4138_, 0);
                    v_isSharedCheck_4146_ = (!crate::leanh::lean_is_exclusive(v___x_4138_)) as u8;
                    if v_isSharedCheck_4146_ == 0 {
                        v___x_4141_ = v___x_4138_;
                        v_isShared_4142_ = v_isSharedCheck_4146_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4139_);
                        crate::leanh::lean_dec(v___x_4138_);
                        v___x_4141_ = crate::leanh::lean_box(0);
                        v_isShared_4142_ = v_isSharedCheck_4146_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4147_ = crate::leanh::lean_ctor_get(v___x_4138_, 0);
                    v_isSharedCheck_4154_ = (!crate::leanh::lean_is_exclusive(v___x_4138_)) as u8;
                    if v_isSharedCheck_4154_ == 0 {
                        v___x_4149_ = v___x_4138_;
                        v_isShared_4150_ = v_isSharedCheck_4154_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4147_);
                        crate::leanh::lean_dec(v___x_4138_);
                        v___x_4149_ = crate::leanh::lean_box(0);
                        v_isShared_4150_ = v_isSharedCheck_4154_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4142_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4141_, 1);
                    v___x_4144_ = v___x_4141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
                    v___x_4144_ = v_reuseFailAlloc_4145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4144_;
            }
            3 => {
                if v_isShared_4150_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4149_, 0);
                    v___x_4152_ = v___x_4149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
                    v___x_4152_ = v_reuseFailAlloc_4153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(
    mut v_a_4155_: *mut crate::leanh::LeanObject,
    mut v___x_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(v_a_4155_, v___x_4156_);
    return v_res_4158_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(
    mut v_linter_4159_: *mut crate::leanh::LeanObject,
    mut v_sz_4160_: usize,
    mut v_i_4161_: usize,
    mut v_bs_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvLinter_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_test_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: usize = 0;
    let mut v___x_4183_: usize = 0;
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4166_ = lean_usize_dec_lt(v_i_4161_, v_sz_4160_);
                if v___x_4166_ == 0 {
                    crate::leanh::lean_dec_ref(v_linter_4159_);
                    v___x_4167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v_bs_4162_);
                    return v___x_4167_;
                } else {
                    v_toEnvLinter_4168_ = crate::leanh::lean_ctor_get(v_linter_4159_, 0);
                    v_test_4169_ = crate::leanh::lean_ctor_get(v_toEnvLinter_4168_, 0);
                    v_v_4170_ = lean_array_uget(v_bs_4162_, v_i_4161_);
                    v___x_4171_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4172_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v_v_4170_);
                    crate::leanh::lean_inc_ref(v_test_4169_);
                    v___f_4173_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed as *mut core::ffi::c_void, 8, 4);
                    crate::leanh::lean_closure_set(v___f_4173_, 0, v___x_4171_);
                    crate::leanh::lean_closure_set(v___f_4173_, 1, v___x_4172_);
                    crate::leanh::lean_closure_set(v___f_4173_, 2, v_test_4169_);
                    crate::leanh::lean_closure_set(v___f_4173_, 3, v_v_4170_);
                    v___x_4174_ = crate::leanh::lean_box(0);
                    v___x_4175_ = l_Lean_Core_wrapAsync___redArg(
                        v___f_4173_,
                        v___x_4174_,
                        v___y_4163_,
                        v___y_4164_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4175_) == 0 {
                        v_a_4176_ = crate::leanh::lean_ctor_get(v___x_4175_, 0);
                        crate::leanh::lean_inc(v_a_4176_);
                        crate::leanh::lean_dec_ref_known(v___x_4175_, 1);
                        v___x_4177_ = crate::leanh::lean_box(0);
                        v___f_4178_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_4178_, 0, v_a_4176_);
                        crate::leanh::lean_closure_set(v___f_4178_, 1, v___x_4177_);
                        v___x_4179_ = lean_io_as_task(v___f_4178_, v___x_4171_);
                        v_bs_x27_4180_ = lean_array_uset(v_bs_4162_, v_i_4161_, v___x_4171_);
                        v___x_4181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4181_, 0, v_v_4170_);
                        crate::leanh::lean_ctor_set(v___x_4181_, 1, v___x_4179_);
                        v___x_4182_ = 1usize;
                        v___x_4183_ = lean_usize_add(v_i_4161_, v___x_4182_);
                        v___x_4184_ = lean_array_uset(v_bs_x27_4180_, v_i_4161_, v___x_4181_);
                        v_i_4161_ = v___x_4183_;
                        v_bs_4162_ = v___x_4184_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_4170_);
                        crate::leanh::lean_dec_ref(v_bs_4162_);
                        crate::leanh::lean_dec_ref(v_linter_4159_);
                        v_a_4186_ = crate::leanh::lean_ctor_get(v___x_4175_, 0);
                        v_isSharedCheck_4193_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4175_)) as u8;
                        if v_isSharedCheck_4193_ == 0 {
                            v___x_4188_ = v___x_4175_;
                            v_isShared_4189_ = v_isSharedCheck_4193_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4186_);
                            crate::leanh::lean_dec(v___x_4175_);
                            v___x_4188_ = crate::leanh::lean_box(0);
                            v_isShared_4189_ = v_isSharedCheck_4193_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4189_ == 0 {
                    v___x_4191_ = v___x_4188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
                    v___x_4191_ = v_reuseFailAlloc_4192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(
    mut v_linter_4194_: *mut crate::leanh::LeanObject,
    mut v_sz_4195_: *mut crate::leanh::LeanObject,
    mut v_i_4196_: *mut crate::leanh::LeanObject,
    mut v_bs_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4201_: usize = 0;
    let mut v_i_boxed_4202_: usize = 0;
    let mut v_res_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4201_ = crate::leanh::lean_unbox_usize(v_sz_4195_);
    crate::leanh::lean_dec(v_sz_4195_);
    v_i_boxed_4202_ = crate::leanh::lean_unbox_usize(v_i_4196_);
    crate::leanh::lean_dec(v_i_4196_);
    v_res_4203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_linter_4194_, v_sz_boxed_4201_, v_i_boxed_4202_, v_bs_4197_, v___y_4198_, v___y_4199_);
    crate::leanh::lean_dec(v___y_4199_);
    crate::leanh::lean_dec_ref(v___y_4198_);
    return v_res_4203_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(
    mut v_decls_4204_: *mut crate::leanh::LeanObject,
    mut v_sz_4205_: usize,
    mut v_i_4206_: usize,
    mut v_bs_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4211_: u8 = 0;
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4218_: usize = 0;
    let mut v___x_4219_: usize = 0;
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: usize = 0;
    let mut v___x_4224_: usize = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4237_: u8 = 0;
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: u8 = 0;
    let mut v_name_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: u8 = 0;
    let mut v___x_4243_: usize = 0;
    let mut v___x_4244_: usize = 0;
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: usize = 0;
    let mut v___x_4247_: usize = 0;
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4211_ = lean_usize_dec_lt(v_i_4206_, v_sz_4205_);
                if v___x_4211_ == 0 {
                    v___x_4212_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4212_, 0, v_bs_4207_);
                    return v___x_4212_;
                } else {
                    v_v_4213_ = lean_array_uget(v_bs_4207_, v_i_4206_);
                    v___x_4214_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4215_ = lean_array_uset(v_bs_4207_, v_i_4206_, v___x_4214_);
                    v___x_4238_ = lean_array_get_size(v_decls_4204_);
                    v___x_4239_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1;
                    v___x_4240_ = lean_nat_dec_lt(v___x_4214_, v___x_4238_);
                    if v___x_4240_ == 0 {
                        v_a_4217_ = v___x_4239_;
                        state = 1;
                        continue;
                    } else {
                        v_name_4241_ = crate::leanh::lean_ctor_get(v_v_4213_, 1);
                        v___x_4242_ = lean_nat_dec_le(v___x_4238_, v___x_4238_);
                        if v___x_4242_ == 0 {
                            if v___x_4240_ == 0 {
                                v_a_4217_ = v___x_4239_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4243_ = 0usize;
                                v___x_4244_ = lean_usize_of_nat(v___x_4238_);
                                v___x_4245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_4241_, v_decls_4204_, v___x_4243_, v___x_4244_, v___x_4239_, v___y_4208_, v___y_4209_);
                                v___y_4228_ = v___x_4245_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_4246_ = 0usize;
                            v___x_4247_ = lean_usize_of_nat(v___x_4238_);
                            v___x_4248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_4241_, v_decls_4204_, v___x_4246_, v___x_4247_, v___x_4239_, v___y_4208_, v___y_4209_);
                            v___y_4228_ = v___x_4248_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_4218_ = lean_array_size(v_a_4217_);
                v___x_4219_ = 0usize;
                crate::leanh::lean_inc(v_v_4213_);
                v___x_4220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_4213_, v_sz_4218_, v___x_4219_, v_a_4217_, v___y_4208_, v___y_4209_);
                if crate::leanh::lean_obj_tag(v___x_4220_) == 0 {
                    v_a_4221_ = crate::leanh::lean_ctor_get(v___x_4220_, 0);
                    crate::leanh::lean_inc(v_a_4221_);
                    crate::leanh::lean_dec_ref_known(v___x_4220_, 1);
                    v___x_4222_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4222_, 0, v_v_4213_);
                    crate::leanh::lean_ctor_set(v___x_4222_, 1, v_a_4221_);
                    v___x_4223_ = 1usize;
                    v___x_4224_ = lean_usize_add(v_i_4206_, v___x_4223_);
                    v___x_4225_ = lean_array_uset(v_bs_x27_4215_, v_i_4206_, v___x_4222_);
                    v_i_4206_ = v___x_4224_;
                    v_bs_4207_ = v___x_4225_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_4215_);
                    crate::leanh::lean_dec(v_v_4213_);
                    return v___x_4220_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4228_) == 0 {
                    v_a_4229_ = crate::leanh::lean_ctor_get(v___y_4228_, 0);
                    crate::leanh::lean_inc(v_a_4229_);
                    crate::leanh::lean_dec_ref_known(v___y_4228_, 1);
                    v_a_4217_ = v_a_4229_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_4215_);
                    crate::leanh::lean_dec(v_v_4213_);
                    v_a_4230_ = crate::leanh::lean_ctor_get(v___y_4228_, 0);
                    v_isSharedCheck_4237_ = (!crate::leanh::lean_is_exclusive(v___y_4228_)) as u8;
                    if v_isSharedCheck_4237_ == 0 {
                        v___x_4232_ = v___y_4228_;
                        v_isShared_4233_ = v_isSharedCheck_4237_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4230_);
                        crate::leanh::lean_dec(v___y_4228_);
                        v___x_4232_ = crate::leanh::lean_box(0);
                        v_isShared_4233_ = v_isSharedCheck_4237_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4233_ == 0 {
                    v___x_4235_ = v___x_4232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
                    v___x_4235_ = v_reuseFailAlloc_4236_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(
    mut v_decls_4249_: *mut crate::leanh::LeanObject,
    mut v_sz_4250_: *mut crate::leanh::LeanObject,
    mut v_i_4251_: *mut crate::leanh::LeanObject,
    mut v_bs_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4256_: usize = 0;
    let mut v_i_boxed_4257_: usize = 0;
    let mut v_res_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4256_ = crate::leanh::lean_unbox_usize(v_sz_4250_);
    crate::leanh::lean_dec(v_sz_4250_);
    v_i_boxed_4257_ = crate::leanh::lean_unbox_usize(v_i_4251_);
    crate::leanh::lean_dec(v_i_4251_);
    v_res_4258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_4249_, v_sz_boxed_4256_, v_i_boxed_4257_, v_bs_4252_, v___y_4253_, v___y_4254_);
    crate::leanh::lean_dec(v___y_4254_);
    crate::leanh::lean_dec_ref(v___y_4253_);
    crate::leanh::lean_dec_ref(v_decls_4249_);
    return v_res_4258_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0()
-> u64 {
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u64 = 0;
    v___x_4259_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4260_ = lean_uint64_of_nat(v___x_4259_);
    return v___x_4260_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(
    mut v_x_4261_: *mut crate::leanh::LeanObject,
    mut v_x_4262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4268_: u8 = 0;
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: u64 = 0;
    let mut v___x_4272_: u64 = 0;
    let mut v___x_4273_: u64 = 0;
    let mut v_fold_4274_: u64 = 0;
    let mut v___x_4275_: u64 = 0;
    let mut v___x_4276_: u64 = 0;
    let mut v___x_4277_: u64 = 0;
    let mut v___x_4278_: usize = 0;
    let mut v___x_4279_: usize = 0;
    let mut v___x_4280_: usize = 0;
    let mut v___x_4281_: usize = 0;
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: u64 = 0;
    let mut v_hash_4290_: u64 = 0;
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4262_) == 0 {
                    return v_x_4261_;
                } else {
                    v_key_4263_ = crate::leanh::lean_ctor_get(v_x_4262_, 0);
                    v_value_4264_ = crate::leanh::lean_ctor_get(v_x_4262_, 1);
                    v_tail_4265_ = crate::leanh::lean_ctor_get(v_x_4262_, 2);
                    v_isSharedCheck_4291_ = (!crate::leanh::lean_is_exclusive(v_x_4262_)) as u8;
                    if v_isSharedCheck_4291_ == 0 {
                        v___x_4267_ = v_x_4262_;
                        v_isShared_4268_ = v_isSharedCheck_4291_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4265_);
                        crate::leanh::lean_inc(v_value_4264_);
                        crate::leanh::lean_inc(v_key_4263_);
                        crate::leanh::lean_dec(v_x_4262_);
                        v___x_4267_ = crate::leanh::lean_box(0);
                        v_isShared_4268_ = v_isSharedCheck_4291_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4269_ = lean_array_get_size(v_x_4261_);
                if crate::leanh::lean_obj_tag(v_key_4263_) == 0 {
                    v___x_4289_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
                    v___y_4271_ = v___x_4289_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4290_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_4263_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4271_ = v_hash_4290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4272_ = 32u64;
                v___x_4273_ = lean_uint64_shift_right(v___y_4271_, v___x_4272_);
                v_fold_4274_ = lean_uint64_xor(v___y_4271_, v___x_4273_);
                v___x_4275_ = 16u64;
                v___x_4276_ = lean_uint64_shift_right(v_fold_4274_, v___x_4275_);
                v___x_4277_ = lean_uint64_xor(v_fold_4274_, v___x_4276_);
                v___x_4278_ = lean_uint64_to_usize(v___x_4277_);
                v___x_4279_ = lean_usize_of_nat(v___x_4269_);
                v___x_4280_ = 1usize;
                v___x_4281_ = lean_usize_sub(v___x_4279_, v___x_4280_);
                v___x_4282_ = lean_usize_land(v___x_4278_, v___x_4281_);
                v___x_4283_ = lean_array_uget_borrowed(v_x_4261_, v___x_4282_);
                crate::leanh::lean_inc(v___x_4283_);
                if v_isShared_4268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4267_, 2, v___x_4283_);
                    v___x_4285_ = v___x_4267_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4288_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_key_4263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4288_, 1, v_value_4264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4288_, 2, v___x_4283_);
                    v___x_4285_ = v_reuseFailAlloc_4288_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4286_ = lean_array_uset(v_x_4261_, v___x_4282_, v___x_4285_);
                v_x_4261_ = v___x_4286_;
                v_x_4262_ = v_tail_4265_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(
    mut v_i_4292_: *mut crate::leanh::LeanObject,
    mut v_source_4293_: *mut crate::leanh::LeanObject,
    mut v_target_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: u8 = 0;
    let mut v_es_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4295_ = lean_array_get_size(v_source_4293_);
                v___x_4296_ = lean_nat_dec_lt(v_i_4292_, v___x_4295_);
                if v___x_4296_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4293_);
                    crate::leanh::lean_dec(v_i_4292_);
                    return v_target_4294_;
                } else {
                    v_es_4297_ = lean_array_fget(v_source_4293_, v_i_4292_);
                    v___x_4298_ = crate::leanh::lean_box(0);
                    v_source_4299_ = lean_array_fset(v_source_4293_, v_i_4292_, v___x_4298_);
                    v_target_4300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_target_4294_, v_es_4297_);
                    v___x_4301_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4302_ = lean_nat_add(v_i_4292_, v___x_4301_);
                    crate::leanh::lean_dec(v_i_4292_);
                    v_i_4292_ = v___x_4302_;
                    v_source_4293_ = v_source_4299_;
                    v_target_4294_ = v_target_4300_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(
    mut v_data_4304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4305_ = lean_array_get_size(v_data_4304_);
    v___x_4306_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4307_ = lean_nat_mul(v___x_4305_, v___x_4306_);
    v___x_4308_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4309_ = crate::leanh::lean_box(0);
    v___x_4310_ = lean_mk_array(v_nbuckets_4307_, v___x_4309_);
    v___x_4311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v___x_4308_, v_data_4304_, v___x_4310_);
    return v___x_4311_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_b_4313_: *mut crate::leanh::LeanObject,
    mut v_x_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4320_: u8 = 0;
    let mut v___x_4321_: u8 = 0;
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4314_) == 0 {
                    crate::leanh::lean_dec(v_b_4313_);
                    crate::leanh::lean_dec(v_a_4312_);
                    return v_x_4314_;
                } else {
                    v_key_4315_ = crate::leanh::lean_ctor_get(v_x_4314_, 0);
                    v_value_4316_ = crate::leanh::lean_ctor_get(v_x_4314_, 1);
                    v_tail_4317_ = crate::leanh::lean_ctor_get(v_x_4314_, 2);
                    v_isSharedCheck_4329_ = (!crate::leanh::lean_is_exclusive(v_x_4314_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_4319_ = v_x_4314_;
                        v_isShared_4320_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4317_);
                        crate::leanh::lean_inc(v_value_4316_);
                        crate::leanh::lean_inc(v_key_4315_);
                        crate::leanh::lean_dec(v_x_4314_);
                        v___x_4319_ = crate::leanh::lean_box(0);
                        v_isShared_4320_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4321_ = lean_name_eq(v_key_4315_, v_a_4312_);
                if v___x_4321_ == 0 {
                    v___x_4322_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_4312_, v_b_4313_, v_tail_4317_);
                    if v_isShared_4320_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4319_, 2, v___x_4322_);
                        v___x_4324_ = v___x_4319_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4325_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_key_4315_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_value_4316_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 2, v___x_4322_);
                        v___x_4324_ = v_reuseFailAlloc_4325_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4316_);
                    crate::leanh::lean_dec(v_key_4315_);
                    if v_isShared_4320_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4319_, 1, v_b_4313_);
                        crate::leanh::lean_ctor_set(v___x_4319_, 0, v_a_4312_);
                        v___x_4327_ = v___x_4319_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4328_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4312_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_b_4313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 2, v_tail_4317_);
                        v___x_4327_ = v_reuseFailAlloc_4328_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4324_;
            }
            3 => {
                return v___x_4327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(
    mut v_a_4330_: *mut crate::leanh::LeanObject,
    mut v_x_4331_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4332_: u8 = 0;
    let mut v_key_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4331_) == 0 {
                    v___x_4332_ = 0;
                    return v___x_4332_;
                } else {
                    v_key_4333_ = crate::leanh::lean_ctor_get(v_x_4331_, 0);
                    v_tail_4334_ = crate::leanh::lean_ctor_get(v_x_4331_, 2);
                    v___x_4335_ = lean_name_eq(v_key_4333_, v_a_4330_);
                    if v___x_4335_ == 0 {
                        v_x_4331_ = v_tail_4334_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4335_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_x_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4339_: u8 = 0;
    let mut v_r_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_4337_, v_x_4338_);
    crate::leanh::lean_dec(v_x_4338_);
    crate::leanh::lean_dec(v_a_4337_);
    v_r_4340_ = crate::leanh::lean_box((v_res_4339_) as usize);
    return v_r_4340_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(
    mut v_m_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_b_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4348_: u8 = 0;
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4351_: u64 = 0;
    let mut v___x_4352_: u64 = 0;
    let mut v___x_4353_: u64 = 0;
    let mut v_fold_4354_: u64 = 0;
    let mut v___x_4355_: u64 = 0;
    let mut v___x_4356_: u64 = 0;
    let mut v___x_4357_: u64 = 0;
    let mut v___x_4358_: usize = 0;
    let mut v___x_4359_: usize = 0;
    let mut v___x_4360_: usize = 0;
    let mut v___x_4361_: usize = 0;
    let mut v___x_4362_: usize = 0;
    let mut v_bkt_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v_val_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u64 = 0;
    let mut v_hash_4390_: u64 = 0;
    let mut v_isSharedCheck_4391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4344_ = crate::leanh::lean_ctor_get(v_m_4341_, 0);
                v_buckets_4345_ = crate::leanh::lean_ctor_get(v_m_4341_, 1);
                v_isSharedCheck_4391_ = (!crate::leanh::lean_is_exclusive(v_m_4341_)) as u8;
                if v_isSharedCheck_4391_ == 0 {
                    v___x_4347_ = v_m_4341_;
                    v_isShared_4348_ = v_isSharedCheck_4391_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4345_);
                    crate::leanh::lean_inc(v_size_4344_);
                    crate::leanh::lean_dec(v_m_4341_);
                    v___x_4347_ = crate::leanh::lean_box(0);
                    v_isShared_4348_ = v_isSharedCheck_4391_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4349_ = lean_array_get_size(v_buckets_4345_);
                if crate::leanh::lean_obj_tag(v_a_4342_) == 0 {
                    v___x_4389_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
                    v___y_4351_ = v___x_4389_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4390_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4342_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4351_ = v_hash_4390_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4352_ = 32u64;
                v___x_4353_ = lean_uint64_shift_right(v___y_4351_, v___x_4352_);
                v_fold_4354_ = lean_uint64_xor(v___y_4351_, v___x_4353_);
                v___x_4355_ = 16u64;
                v___x_4356_ = lean_uint64_shift_right(v_fold_4354_, v___x_4355_);
                v___x_4357_ = lean_uint64_xor(v_fold_4354_, v___x_4356_);
                v___x_4358_ = lean_uint64_to_usize(v___x_4357_);
                v___x_4359_ = lean_usize_of_nat(v___x_4349_);
                v___x_4360_ = 1usize;
                v___x_4361_ = lean_usize_sub(v___x_4359_, v___x_4360_);
                v___x_4362_ = lean_usize_land(v___x_4358_, v___x_4361_);
                v_bkt_4363_ = lean_array_uget_borrowed(v_buckets_4345_, v___x_4362_);
                v___x_4364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_4342_, v_bkt_4363_);
                if v___x_4364_ == 0 {
                    v___x_4365_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4366_ = lean_nat_add(v_size_4344_, v___x_4365_);
                    crate::leanh::lean_dec(v_size_4344_);
                    crate::leanh::lean_inc(v_bkt_4363_);
                    v___x_4367_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4367_, 0, v_a_4342_);
                    crate::leanh::lean_ctor_set(v___x_4367_, 1, v_b_4343_);
                    crate::leanh::lean_ctor_set(v___x_4367_, 2, v_bkt_4363_);
                    v_buckets_x27_4368_ =
                        lean_array_uset(v_buckets_4345_, v___x_4362_, v___x_4367_);
                    v___x_4369_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4370_ = lean_nat_mul(v_size_x27_4366_, v___x_4369_);
                    v___x_4371_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4372_ = lean_nat_div(v___x_4370_, v___x_4371_);
                    crate::leanh::lean_dec(v___x_4370_);
                    v___x_4373_ = lean_array_get_size(v_buckets_x27_4368_);
                    v___x_4374_ = lean_nat_dec_le(v___x_4372_, v___x_4373_);
                    crate::leanh::lean_dec(v___x_4372_);
                    if v___x_4374_ == 0 {
                        v_val_4375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_buckets_x27_4368_);
                        if v_isShared_4348_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4347_, 1, v_val_4375_);
                            crate::leanh::lean_ctor_set(v___x_4347_, 0, v_size_x27_4366_);
                            v___x_4377_ = v___x_4347_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4378_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4378_,
                                0,
                                v_size_x27_4366_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 1, v_val_4375_);
                            v___x_4377_ = v_reuseFailAlloc_4378_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4348_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4347_, 1, v_buckets_x27_4368_);
                            crate::leanh::lean_ctor_set(v___x_4347_, 0, v_size_x27_4366_);
                            v___x_4380_ = v___x_4347_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4381_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4381_,
                                0,
                                v_size_x27_4366_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4381_,
                                1,
                                v_buckets_x27_4368_,
                            );
                            v___x_4380_ = v_reuseFailAlloc_4381_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4363_);
                    v___x_4382_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4383_ =
                        lean_array_uset(v_buckets_4345_, v___x_4362_, v___x_4382_);
                    v___x_4384_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_4342_, v_b_4343_, v_bkt_4363_);
                    v___x_4385_ = lean_array_uset(v_buckets_x27_4383_, v___x_4362_, v___x_4384_);
                    if v_isShared_4348_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4347_, 1, v___x_4385_);
                        v___x_4387_ = v___x_4347_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4388_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_size_4344_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 1, v___x_4385_);
                        v___x_4387_ = v_reuseFailAlloc_4388_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4377_;
            }
            4 => {
                return v___x_4380_;
            }
            5 => {
                return v___x_4387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0;
    v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(
    mut v_as_4395_: *mut crate::leanh::LeanObject,
    mut v_sz_4396_: usize,
    mut v_i_4397_: usize,
    mut v_b_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: usize = 0;
    let mut v___x_4403_: usize = 0;
    let mut v___x_4405_: u8 = 0;
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v_val_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4405_ = lean_usize_dec_lt(v_i_4397_, v_sz_4396_);
                if v___x_4405_ == 0 {
                    v___x_4406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4406_, 0, v_b_4398_);
                    return v___x_4406_;
                } else {
                    v_a_4407_ = lean_array_uget(v_as_4395_, v_i_4397_);
                    v_fst_4408_ = crate::leanh::lean_ctor_get(v_a_4407_, 0);
                    v_snd_4409_ = crate::leanh::lean_ctor_get(v_a_4407_, 1);
                    v_isSharedCheck_4425_ = (!crate::leanh::lean_is_exclusive(v_a_4407_)) as u8;
                    if v_isSharedCheck_4425_ == 0 {
                        v___x_4411_ = v_a_4407_;
                        v_isShared_4412_ = v_isSharedCheck_4425_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4409_);
                        crate::leanh::lean_inc(v_fst_4408_);
                        crate::leanh::lean_dec(v_a_4407_);
                        v___x_4411_ = crate::leanh::lean_box(0);
                        v_isShared_4412_ = v_isSharedCheck_4425_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4402_ = 1usize;
                v___x_4403_ = lean_usize_add(v_i_4397_, v___x_4402_);
                v_i_4397_ = v___x_4403_;
                v_b_4398_ = v_a_4401_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4416_ = lean_task_get_own(v_snd_4409_);
                if crate::leanh::lean_obj_tag(v___x_4416_) == 0 {
                    v_a_4417_ = crate::leanh::lean_ctor_get(v___x_4416_, 0);
                    crate::leanh::lean_inc(v_a_4417_);
                    crate::leanh::lean_dec_ref_known(v___x_4416_, 1);
                    v___x_4418_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1);
                    v___x_4419_ = l_Lean_Exception_toMessageData(v_a_4417_);
                    if v_isShared_4412_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4411_, 7);
                        crate::leanh::lean_ctor_set(v___x_4411_, 1, v___x_4419_);
                        crate::leanh::lean_ctor_set(v___x_4411_, 0, v___x_4418_);
                        v___x_4421_ = v___x_4411_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4422_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4418_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 1, v___x_4419_);
                        v___x_4421_ = v_reuseFailAlloc_4422_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4411_);
                    v_a_4423_ = crate::leanh::lean_ctor_get(v___x_4416_, 0);
                    crate::leanh::lean_inc(v_a_4423_);
                    crate::leanh::lean_dec_ref_known(v___x_4416_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4423_) == 1 {
                        v_val_4424_ = crate::leanh::lean_ctor_get(v_a_4423_, 0);
                        crate::leanh::lean_inc(v_val_4424_);
                        crate::leanh::lean_dec_ref_known(v_a_4423_, 1);
                        v_val_4414_ = v_val_4424_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4423_);
                        crate::leanh::lean_dec(v_fst_4408_);
                        v_a_4401_ = v_b_4398_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4415_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_4398_, v_fst_4408_, v_val_4414_);
                v_a_4401_ = v___x_4415_;
                state = 1;
                continue;
            }
            4 => {
                v_val_4414_ = v___x_4421_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(
    mut v_as_4426_: *mut crate::leanh::LeanObject,
    mut v_sz_4427_: *mut crate::leanh::LeanObject,
    mut v_i_4428_: *mut crate::leanh::LeanObject,
    mut v_b_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4431_: usize = 0;
    let mut v_i_boxed_4432_: usize = 0;
    let mut v_res_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4431_ = crate::leanh::lean_unbox_usize(v_sz_4427_);
    crate::leanh::lean_dec(v_sz_4427_);
    v_i_boxed_4432_ = crate::leanh::lean_unbox_usize(v_i_4428_);
    crate::leanh::lean_dec(v_i_4428_);
    v_res_4433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_4426_, v_sz_boxed_4431_, v_i_boxed_4432_, v_b_4429_);
    crate::leanh::lean_dec_ref(v_as_4426_);
    return v_res_4433_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4434_ = crate::leanh::lean_box(0);
    v___x_4435_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4436_ = lean_mk_array(v___x_4435_, v___x_4434_);
    return v___x_4436_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4437_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
    v___x_4438_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4439_, 0, v___x_4438_);
    crate::leanh::lean_ctor_set(v___x_4439_, 1, v___x_4437_);
    return v___x_4439_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(
    mut v_sz_4440_: usize,
    mut v_i_4441_: usize,
    mut v_bs_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4446_: u8 = 0;
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4456_: usize = 0;
    let mut v___x_4457_: usize = 0;
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: usize = 0;
    let mut v___x_4464_: usize = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4446_ = lean_usize_dec_lt(v_i_4441_, v_sz_4440_);
                if v___x_4446_ == 0 {
                    v___x_4447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4447_, 0, v_bs_4442_);
                    return v___x_4447_;
                } else {
                    v_v_4448_ = lean_array_uget(v_bs_4442_, v_i_4441_);
                    v_fst_4449_ = crate::leanh::lean_ctor_get(v_v_4448_, 0);
                    v_snd_4450_ = crate::leanh::lean_ctor_get(v_v_4448_, 1);
                    v_isSharedCheck_4476_ = (!crate::leanh::lean_is_exclusive(v_v_4448_)) as u8;
                    if v_isSharedCheck_4476_ == 0 {
                        v___x_4452_ = v_v_4448_;
                        v_isShared_4453_ = v_isSharedCheck_4476_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4450_);
                        crate::leanh::lean_inc(v_fst_4449_);
                        crate::leanh::lean_dec(v_v_4448_);
                        v___x_4452_ = crate::leanh::lean_box(0);
                        v_isShared_4453_ = v_isSharedCheck_4476_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4454_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4455_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
                v_sz_4456_ = lean_array_size(v_snd_4450_);
                v___x_4457_ = 0usize;
                v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_snd_4450_, v_sz_4456_, v___x_4457_, v___x_4455_);
                crate::leanh::lean_dec(v_snd_4450_);
                if crate::leanh::lean_obj_tag(v___x_4458_) == 0 {
                    v_a_4459_ = crate::leanh::lean_ctor_get(v___x_4458_, 0);
                    crate::leanh::lean_inc(v_a_4459_);
                    crate::leanh::lean_dec_ref_known(v___x_4458_, 1);
                    v_bs_x27_4460_ = lean_array_uset(v_bs_4442_, v_i_4441_, v___x_4454_);
                    if v_isShared_4453_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4452_, 1, v_a_4459_);
                        v___x_4462_ = v___x_4452_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4467_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_fst_4449_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4467_, 1, v_a_4459_);
                        v___x_4462_ = v_reuseFailAlloc_4467_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4452_);
                    crate::leanh::lean_dec(v_fst_4449_);
                    crate::leanh::lean_dec_ref(v_bs_4442_);
                    v_a_4468_ = crate::leanh::lean_ctor_get(v___x_4458_, 0);
                    v_isSharedCheck_4475_ = (!crate::leanh::lean_is_exclusive(v___x_4458_)) as u8;
                    if v_isSharedCheck_4475_ == 0 {
                        v___x_4470_ = v___x_4458_;
                        v_isShared_4471_ = v_isSharedCheck_4475_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4468_);
                        crate::leanh::lean_dec(v___x_4458_);
                        v___x_4470_ = crate::leanh::lean_box(0);
                        v_isShared_4471_ = v_isSharedCheck_4475_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4463_ = 1usize;
                v___x_4464_ = lean_usize_add(v_i_4441_, v___x_4463_);
                v___x_4465_ = lean_array_uset(v_bs_x27_4460_, v_i_4441_, v___x_4462_);
                v_i_4441_ = v___x_4464_;
                v_bs_4442_ = v___x_4465_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4471_ == 0 {
                    v___x_4473_ = v___x_4470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___boxed(
    mut v_sz_4477_: *mut crate::leanh::LeanObject,
    mut v_i_4478_: *mut crate::leanh::LeanObject,
    mut v_bs_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4483_: usize = 0;
    let mut v_i_boxed_4484_: usize = 0;
    let mut v_res_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4483_ = crate::leanh::lean_unbox_usize(v_sz_4477_);
    crate::leanh::lean_dec(v_sz_4477_);
    v_i_boxed_4484_ = crate::leanh::lean_unbox_usize(v_i_4478_);
    crate::leanh::lean_dec(v_i_4478_);
    v_res_4485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_boxed_4483_, v_i_boxed_4484_, v_bs_4479_, v___y_4480_, v___y_4481_);
    crate::leanh::lean_dec(v___y_4481_);
    crate::leanh::lean_dec_ref(v___y_4480_);
    return v_res_4485_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_lintCore(
    mut v_decls_4486_: *mut crate::leanh::LeanObject,
    mut v_linters_4487_: *mut crate::leanh::LeanObject,
    mut v_a_4488_: *mut crate::leanh::LeanObject,
    mut v_a_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4491_: usize = 0;
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4495_: usize = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4491_ = lean_array_size(v_linters_4487_);
                v___x_4492_ = 0usize;
                v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_4486_, v_sz_4491_, v___x_4492_, v_linters_4487_, v_a_4488_, v_a_4489_);
                if crate::leanh::lean_obj_tag(v___x_4493_) == 0 {
                    v_a_4494_ = crate::leanh::lean_ctor_get(v___x_4493_, 0);
                    crate::leanh::lean_inc(v_a_4494_);
                    crate::leanh::lean_dec_ref_known(v___x_4493_, 1);
                    v_sz_4495_ = lean_array_size(v_a_4494_);
                    v___x_4496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_4495_, v___x_4492_, v_a_4494_, v_a_4488_, v_a_4489_);
                    return v___x_4496_;
                } else {
                    v_a_4497_ = crate::leanh::lean_ctor_get(v___x_4493_, 0);
                    v_isSharedCheck_4504_ = (!crate::leanh::lean_is_exclusive(v___x_4493_)) as u8;
                    if v_isSharedCheck_4504_ == 0 {
                        v___x_4499_ = v___x_4493_;
                        v_isShared_4500_ = v_isSharedCheck_4504_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4497_);
                        crate::leanh::lean_dec(v___x_4493_);
                        v___x_4499_ = crate::leanh::lean_box(0);
                        v_isShared_4500_ = v_isSharedCheck_4504_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4500_ == 0 {
                    v___x_4502_ = v___x_4499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_lintCore___boxed(
    mut v_decls_4505_: *mut crate::leanh::LeanObject,
    mut v_linters_4506_: *mut crate::leanh::LeanObject,
    mut v_a_4507_: *mut crate::leanh::LeanObject,
    mut v_a_4508_: *mut crate::leanh::LeanObject,
    mut v_a_4509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4510_ =
        l_Lean_Linter_EnvLinter_lintCore(v_decls_4505_, v_linters_4506_, v_a_4507_, v_a_4508_);
    crate::leanh::lean_dec(v_a_4508_);
    crate::leanh::lean_dec_ref(v_a_4507_);
    crate::leanh::lean_dec_ref(v_decls_4505_);
    return v_res_4510_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(
    mut v_00_u03b2_4511_: *mut crate::leanh::LeanObject,
    mut v_m_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
    mut v_b_4514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4515_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_m_4512_, v_a_4513_, v_b_4514_);
    return v___x_4515_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(
    mut v_as_4516_: *mut crate::leanh::LeanObject,
    mut v_sz_4517_: usize,
    mut v_i_4518_: usize,
    mut v_b_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_4516_, v_sz_4517_, v_i_4518_, v_b_4519_);
    return v___x_4523_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(
    mut v_as_4524_: *mut crate::leanh::LeanObject,
    mut v_sz_4525_: *mut crate::leanh::LeanObject,
    mut v_i_4526_: *mut crate::leanh::LeanObject,
    mut v_b_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4531_: usize = 0;
    let mut v_i_boxed_4532_: usize = 0;
    let mut v_res_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4531_ = crate::leanh::lean_unbox_usize(v_sz_4525_);
    crate::leanh::lean_dec(v_sz_4525_);
    v_i_boxed_4532_ = crate::leanh::lean_unbox_usize(v_i_4526_);
    crate::leanh::lean_dec(v_i_4526_);
    v_res_4533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(v_as_4524_, v_sz_boxed_4531_, v_i_boxed_4532_, v_b_4527_, v___y_4528_, v___y_4529_);
    crate::leanh::lean_dec(v___y_4529_);
    crate::leanh::lean_dec_ref(v___y_4528_);
    crate::leanh::lean_dec_ref(v_as_4524_);
    return v_res_4533_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(
    mut v_linter_4534_: *mut crate::leanh::LeanObject,
    mut v_decl_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4539_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_4534_, v_decl_4535_, v___y_4537_);
    return v___x_4539_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(
    mut v_linter_4540_: *mut crate::leanh::LeanObject,
    mut v_decl_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4545_ =
        l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(
            v_linter_4540_,
            v_decl_4541_,
            v___y_4542_,
            v___y_4543_,
        );
    crate::leanh::lean_dec(v___y_4543_);
    crate::leanh::lean_dec_ref(v___y_4542_);
    crate::leanh::lean_dec(v_linter_4540_);
    return v_res_4545_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(
    mut v_00_u03b2_4546_: *mut crate::leanh::LeanObject,
    mut v_a_4547_: *mut crate::leanh::LeanObject,
    mut v_x_4548_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4549_: u8 = 0;
    v___x_4549_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_4547_, v_x_4548_);
    return v___x_4549_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(
    mut v_00_u03b2_4550_: *mut crate::leanh::LeanObject,
    mut v_a_4551_: *mut crate::leanh::LeanObject,
    mut v_x_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4553_: u8 = 0;
    let mut v_r_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4553_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(v_00_u03b2_4550_, v_a_4551_, v_x_4552_);
    crate::leanh::lean_dec(v_x_4552_);
    crate::leanh::lean_dec(v_a_4551_);
    v_r_4554_ = crate::leanh::lean_box((v_res_4553_) as usize);
    return v_r_4554_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(
    mut v_00_u03b2_4555_: *mut crate::leanh::LeanObject,
    mut v_data_4556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4557_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_data_4556_);
    return v___x_4557_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(
    mut v_00_u03b2_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
    mut v_b_4560_: *mut crate::leanh::LeanObject,
    mut v_x_4561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4562_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_4559_, v_b_4560_, v_x_4561_);
    return v___x_4562_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4563_: *mut crate::leanh::LeanObject,
    mut v_i_4564_: *mut crate::leanh::LeanObject,
    mut v_source_4565_: *mut crate::leanh::LeanObject,
    mut v_target_4566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4567_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v_i_4564_, v_source_4565_, v_target_4566_);
    return v___x_4567_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9(
    mut v_00_u03b2_4568_: *mut crate::leanh::LeanObject,
    mut v_x_4569_: *mut crate::leanh::LeanObject,
    mut v_x_4570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4571_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_x_4569_, v_x_4570_);
    return v___x_4571_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(
    mut v_a_4572_: *mut crate::leanh::LeanObject,
    mut v_fallback_4573_: *mut crate::leanh::LeanObject,
    mut v_x_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4574_) == 0 {
                    crate::leanh::lean_inc(v_fallback_4573_);
                    return v_fallback_4573_;
                } else {
                    v_key_4575_ = crate::leanh::lean_ctor_get(v_x_4574_, 0);
                    v_value_4576_ = crate::leanh::lean_ctor_get(v_x_4574_, 1);
                    v_tail_4577_ = crate::leanh::lean_ctor_get(v_x_4574_, 2);
                    v___x_4578_ = lean_name_eq(v_key_4575_, v_a_4572_);
                    if v___x_4578_ == 0 {
                        v_x_4574_ = v_tail_4577_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4576_);
                        return v_value_4576_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(
    mut v_a_4580_: *mut crate::leanh::LeanObject,
    mut v_fallback_4581_: *mut crate::leanh::LeanObject,
    mut v_x_4582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4583_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_4580_, v_fallback_4581_, v_x_4582_);
    crate::leanh::lean_dec(v_x_4582_);
    crate::leanh::lean_dec(v_fallback_4581_);
    crate::leanh::lean_dec(v_a_4580_);
    return v_res_4583_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(
    mut v_m_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_fallback_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4590_: u64 = 0;
    let mut v___x_4591_: u64 = 0;
    let mut v___x_4592_: u64 = 0;
    let mut v_fold_4593_: u64 = 0;
    let mut v___x_4594_: u64 = 0;
    let mut v___x_4595_: u64 = 0;
    let mut v___x_4596_: u64 = 0;
    let mut v___x_4597_: usize = 0;
    let mut v___x_4598_: usize = 0;
    let mut v___x_4599_: usize = 0;
    let mut v___x_4600_: usize = 0;
    let mut v___x_4601_: usize = 0;
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: u64 = 0;
    let mut v_hash_4605_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4587_ = crate::leanh::lean_ctor_get(v_m_4584_, 1);
                v___x_4588_ = lean_array_get_size(v_buckets_4587_);
                if crate::leanh::lean_obj_tag(v_a_4585_) == 0 {
                    v___x_4604_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
                    v___y_4590_ = v___x_4604_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4605_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4585_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4590_ = v_hash_4605_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4591_ = 32u64;
                v___x_4592_ = lean_uint64_shift_right(v___y_4590_, v___x_4591_);
                v_fold_4593_ = lean_uint64_xor(v___y_4590_, v___x_4592_);
                v___x_4594_ = 16u64;
                v___x_4595_ = lean_uint64_shift_right(v_fold_4593_, v___x_4594_);
                v___x_4596_ = lean_uint64_xor(v_fold_4593_, v___x_4595_);
                v___x_4597_ = lean_uint64_to_usize(v___x_4596_);
                v___x_4598_ = lean_usize_of_nat(v___x_4588_);
                v___x_4599_ = 1usize;
                v___x_4600_ = lean_usize_sub(v___x_4598_, v___x_4599_);
                v___x_4601_ = lean_usize_land(v___x_4597_, v___x_4600_);
                v___x_4602_ = lean_array_uget_borrowed(v_buckets_4587_, v___x_4601_);
                v___x_4603_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_4585_, v_fallback_4586_, v___x_4602_);
                return v___x_4603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(
    mut v_m_4606_: *mut crate::leanh::LeanObject,
    mut v_a_4607_: *mut crate::leanh::LeanObject,
    mut v_fallback_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_4606_, v_a_4607_, v_fallback_4608_);
    crate::leanh::lean_dec(v_fallback_4608_);
    crate::leanh::lean_dec(v_a_4607_);
    crate::leanh::lean_dec_ref(v_m_4606_);
    return v_res_4609_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(
    mut v_a_4610_: *mut crate::leanh::LeanObject,
    mut v_hi_4611_: *mut crate::leanh::LeanObject,
    mut v_pivot_4612_: *mut crate::leanh::LeanObject,
    mut v_as_4613_: *mut crate::leanh::LeanObject,
    mut v_i_4614_: *mut crate::leanh::LeanObject,
    mut v_k_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: u8 = 0;
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4616_ = lean_nat_dec_lt(v_k_4615_, v_hi_4611_);
                if v___x_4616_ == 0 {
                    crate::leanh::lean_dec(v_k_4615_);
                    v___x_4617_ = lean_array_fswap(v_as_4613_, v_i_4614_, v_hi_4611_);
                    v___x_4618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4618_, 0, v_i_4614_);
                    crate::leanh::lean_ctor_set(v___x_4618_, 1, v___x_4617_);
                    return v___x_4618_;
                } else {
                    v___x_4619_ = lean_array_fget_borrowed(v_as_4613_, v_k_4615_);
                    v_fst_4620_ = crate::leanh::lean_ctor_get(v___x_4619_, 0);
                    v_fst_4621_ = crate::leanh::lean_ctor_get(v_pivot_4612_, 0);
                    v___x_4622_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_4610_, v_fst_4620_, v___x_4622_);
                    v___x_4624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_4610_, v_fst_4621_, v___x_4622_);
                    v___x_4625_ = lean_nat_dec_lt(v___x_4623_, v___x_4624_);
                    crate::leanh::lean_dec(v___x_4624_);
                    crate::leanh::lean_dec(v___x_4623_);
                    if v___x_4625_ == 0 {
                        v___x_4626_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4627_ = lean_nat_add(v_k_4615_, v___x_4626_);
                        crate::leanh::lean_dec(v_k_4615_);
                        v_k_4615_ = v___x_4627_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4629_ = lean_array_fswap(v_as_4613_, v_i_4614_, v_k_4615_);
                        v___x_4630_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4631_ = lean_nat_add(v_i_4614_, v___x_4630_);
                        crate::leanh::lean_dec(v_i_4614_);
                        v___x_4632_ = lean_nat_add(v_k_4615_, v___x_4630_);
                        crate::leanh::lean_dec(v_k_4615_);
                        v_as_4613_ = v___x_4629_;
                        v_i_4614_ = v___x_4631_;
                        v_k_4615_ = v___x_4632_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(
    mut v_a_4634_: *mut crate::leanh::LeanObject,
    mut v_hi_4635_: *mut crate::leanh::LeanObject,
    mut v_pivot_4636_: *mut crate::leanh::LeanObject,
    mut v_as_4637_: *mut crate::leanh::LeanObject,
    mut v_i_4638_: *mut crate::leanh::LeanObject,
    mut v_k_4639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_4634_, v_hi_4635_, v_pivot_4636_, v_as_4637_, v_i_4638_, v_k_4639_);
    crate::leanh::lean_dec_ref(v_pivot_4636_);
    crate::leanh::lean_dec(v_hi_4635_);
    crate::leanh::lean_dec_ref(v_a_4634_);
    return v_res_4640_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(
    mut v_a_4641_: *mut crate::leanh::LeanObject,
    mut v_x_4642_: *mut crate::leanh::LeanObject,
    mut v_x_4643_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: u8 = 0;
    v_fst_4644_ = crate::leanh::lean_ctor_get(v_x_4642_, 0);
    v_fst_4645_ = crate::leanh::lean_ctor_get(v_x_4643_, 0);
    v___x_4646_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_4641_, v_fst_4644_, v___x_4646_);
    v___x_4648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_4641_, v_fst_4645_, v___x_4646_);
    v___x_4649_ = lean_nat_dec_lt(v___x_4647_, v___x_4648_);
    crate::leanh::lean_dec(v___x_4648_);
    crate::leanh::lean_dec(v___x_4647_);
    return v___x_4649_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(
    mut v_a_4650_: *mut crate::leanh::LeanObject,
    mut v_x_4651_: *mut crate::leanh::LeanObject,
    mut v_x_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: u8 = 0;
    let mut v_r_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_4650_, v_x_4651_, v_x_4652_);
    crate::leanh::lean_dec_ref(v_x_4652_);
    crate::leanh::lean_dec_ref(v_x_4651_);
    crate::leanh::lean_dec_ref(v_a_4650_);
    v_r_4654_ = crate::leanh::lean_box((v_res_4653_) as usize);
    return v_r_4654_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(
    mut v_a_4655_: *mut crate::leanh::LeanObject,
    mut v_n_4656_: *mut crate::leanh::LeanObject,
    mut v_as_4657_: *mut crate::leanh::LeanObject,
    mut v_lo_4658_: *mut crate::leanh::LeanObject,
    mut v_hi_4659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: u8 = 0;
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: u8 = 0;
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: u8 = 0;
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4671_ = lean_nat_dec_lt(v_lo_4658_, v_hi_4659_);
                if v___x_4671_ == 0 {
                    crate::leanh::lean_dec(v_lo_4658_);
                    return v_as_4657_;
                } else {
                    v___x_4672_ = lean_nat_add(v_lo_4658_, v_hi_4659_);
                    v___x_4673_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_4674_ = lean_nat_shiftr(v___x_4672_, v___x_4673_);
                    crate::leanh::lean_dec(v___x_4672_);
                    v___x_4687_ = lean_array_fget_borrowed(v_as_4657_, v_mid_4674_);
                    v___x_4688_ = lean_array_fget_borrowed(v_as_4657_, v_lo_4658_);
                    v___x_4689_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_4655_, v___x_4687_, v___x_4688_);
                    if v___x_4689_ == 0 {
                        v___y_4682_ = v_as_4657_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4690_ = lean_array_fswap(v_as_4657_, v_lo_4658_, v_mid_4674_);
                        v___y_4682_ = v___x_4690_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_4662_ = lean_array_fget(v___y_4661_, v_hi_4659_);
                crate::leanh::lean_inc_n(v_lo_4658_, 2);
                v___x_4663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_4655_, v_hi_4659_, v_pivot_4662_, v___y_4661_, v_lo_4658_, v_lo_4658_);
                crate::leanh::lean_dec(v_pivot_4662_);
                v_fst_4664_ = crate::leanh::lean_ctor_get(v___x_4663_, 0);
                crate::leanh::lean_inc(v_fst_4664_);
                v_snd_4665_ = crate::leanh::lean_ctor_get(v___x_4663_, 1);
                crate::leanh::lean_inc(v_snd_4665_);
                crate::leanh::lean_dec_ref(v___x_4663_);
                v___x_4666_ = lean_nat_dec_le(v_hi_4659_, v_fst_4664_);
                if v___x_4666_ == 0 {
                    v___x_4667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_4655_, v_n_4656_, v_snd_4665_, v_lo_4658_, v_fst_4664_);
                    v___x_4668_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4669_ = lean_nat_add(v_fst_4664_, v___x_4668_);
                    crate::leanh::lean_dec(v_fst_4664_);
                    v_as_4657_ = v___x_4667_;
                    v_lo_4658_ = v___x_4669_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_4664_);
                    crate::leanh::lean_dec(v_lo_4658_);
                    return v_snd_4665_;
                }
            }
            2 => {
                v___x_4677_ = lean_array_fget_borrowed(v___y_4676_, v_mid_4674_);
                v___x_4678_ = lean_array_fget_borrowed(v___y_4676_, v_hi_4659_);
                v___x_4679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_4655_, v___x_4677_, v___x_4678_);
                if v___x_4679_ == 0 {
                    crate::leanh::lean_dec(v_mid_4674_);
                    v___y_4661_ = v___y_4676_;
                    state = 1;
                    continue;
                } else {
                    v___x_4680_ = lean_array_fswap(v___y_4676_, v_mid_4674_, v_hi_4659_);
                    crate::leanh::lean_dec(v_mid_4674_);
                    v___y_4661_ = v___x_4680_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4683_ = lean_array_fget_borrowed(v___y_4682_, v_hi_4659_);
                v___x_4684_ = lean_array_fget_borrowed(v___y_4682_, v_lo_4658_);
                v___x_4685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_4655_, v___x_4683_, v___x_4684_);
                if v___x_4685_ == 0 {
                    v___y_4676_ = v___y_4682_;
                    state = 2;
                    continue;
                } else {
                    v___x_4686_ = lean_array_fswap(v___y_4682_, v_lo_4658_, v_hi_4659_);
                    v___y_4676_ = v___x_4686_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(
    mut v_a_4691_: *mut crate::leanh::LeanObject,
    mut v_n_4692_: *mut crate::leanh::LeanObject,
    mut v_as_4693_: *mut crate::leanh::LeanObject,
    mut v_lo_4694_: *mut crate::leanh::LeanObject,
    mut v_hi_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_4691_, v_n_4692_, v_as_4693_, v_lo_4694_, v_hi_4695_);
    crate::leanh::lean_dec(v_hi_4695_);
    crate::leanh::lean_dec(v_n_4692_);
    crate::leanh::lean_dec_ref(v_a_4691_);
    return v_res_4696_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(
    mut v_declName_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: u8 = 0;
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4700_ = lean_st_ref_get(v___y_4698_);
    v_env_4701_ = crate::leanh::lean_ctor_get(v___x_4700_, 0);
    crate::leanh::lean_inc_ref(v_env_4701_);
    crate::leanh::lean_dec(v___x_4700_);
    v___x_4702_ = l_Lean_isRecCore(v_env_4701_, v_declName_4697_);
    v___x_4703_ = crate::leanh::lean_box((v___x_4702_) as usize);
    v___x_4704_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4704_, 0, v___x_4703_);
    return v___x_4704_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(
    mut v_declName_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4708_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_4705_, v___y_4706_);
    crate::leanh::lean_dec(v___y_4706_);
    return v_res_4708_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(
    mut v_declName_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: u8 = 0;
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4712_ = lean_st_ref_get(v___y_4710_);
    v_env_4713_ = crate::leanh::lean_ctor_get(v___x_4712_, 0);
    crate::leanh::lean_inc_ref(v_env_4713_);
    crate::leanh::lean_dec(v___x_4712_);
    v___x_4714_ = lean_st_ref_get(v___y_4710_);
    v_env_4715_ = crate::leanh::lean_ctor_get(v___x_4714_, 0);
    crate::leanh::lean_inc_ref(v_env_4715_);
    crate::leanh::lean_dec(v___x_4714_);
    v___x_4716_ = l_Lean_declRangeExt;
    v_toEnvExtension_4717_ = crate::leanh::lean_ctor_get(v___x_4716_, 0);
    v_asyncMode_4718_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4717_, 2);
    v___x_4719_ = l_Lean_instInhabitedDeclarationRanges_default;
    v___x_4720_ = 0;
    crate::leanh::lean_inc(v_declName_4709_);
    v___x_4721_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_4719_,
        v___x_4716_,
        v_env_4713_,
        v_declName_4709_,
        v_asyncMode_4718_,
        v___x_4720_,
    );
    if crate::leanh::lean_obj_tag(v___x_4721_) == 0 {
        let mut v___x_4722_: u8 = 0;
        let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4722_ = 1;
        v___x_4723_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
            v___x_4719_,
            v___x_4716_,
            v_env_4715_,
            v_declName_4709_,
            v_asyncMode_4718_,
            v___x_4722_,
        );
        v___x_4724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4724_, 0, v___x_4723_);
        return v___x_4724_;
    } else {
        let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_4715_);
        crate::leanh::lean_dec(v_declName_4709_);
        v___x_4725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4725_, 0, v___x_4721_);
        return v___x_4725_;
    }
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(
    mut v_declName_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4729_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_4726_, v___y_4727_);
    crate::leanh::lean_dec(v___y_4727_);
    return v_res_4729_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(
    mut v_declName_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ranges_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4750_: u8 = 0;
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: u8 = 0;
    let mut v___x_4755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4741_ = lean_st_ref_get(v___y_4732_);
                v_env_4742_ = crate::leanh::lean_ctor_get(v___x_4741_, 0);
                crate::leanh::lean_inc_ref_n(v_env_4742_, 2);
                crate::leanh::lean_dec(v___x_4741_);
                crate::leanh::lean_inc_n(v_declName_4730_, 2);
                v___x_4743_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_4730_, v___y_4732_);
                v_a_4744_ = crate::leanh::lean_ctor_get(v___x_4743_, 0);
                crate::leanh::lean_inc(v_a_4744_);
                crate::leanh::lean_dec_ref(v___x_4743_);
                v___x_4754_ = l_Lean_isAuxRecursor(v_env_4742_, v_declName_4730_);
                if v___x_4754_ == 0 {
                    crate::leanh::lean_inc(v_declName_4730_);
                    v___x_4755_ = l_Lean_isNoConfusion(v_env_4742_, v_declName_4730_);
                    v___y_4750_ = v___x_4755_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_4742_);
                    v___y_4750_ = v___x_4754_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_ranges_4735_) == 0 {
                    v___x_4736_ = l_Lean_builtinDeclRanges;
                    v___x_4737_ = lean_st_ref_get(v___x_4736_);
                    v___x_4738_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4737_, v_declName_4730_);
                    crate::leanh::lean_dec(v_declName_4730_);
                    crate::leanh::lean_dec(v___x_4737_);
                    v___x_4739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4739_, 0, v___x_4738_);
                    return v___x_4739_;
                } else {
                    crate::leanh::lean_dec(v_declName_4730_);
                    v___x_4740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4740_, 0, v_ranges_4735_);
                    return v___x_4740_;
                }
            }
            2 => {
                v___x_4746_ = l_Lean_Name_getPrefix(v_declName_4730_);
                v___x_4747_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v___x_4746_, v___y_4732_);
                v_a_4748_ = crate::leanh::lean_ctor_get(v___x_4747_, 0);
                crate::leanh::lean_inc(v_a_4748_);
                crate::leanh::lean_dec_ref(v___x_4747_);
                v_ranges_4735_ = v_a_4748_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_4750_ == 0 {
                    v___x_4751_ = (crate::leanh::lean_unbox(v_a_4744_) as u8);
                    crate::leanh::lean_dec(v_a_4744_);
                    if v___x_4751_ == 0 {
                        crate::leanh::lean_inc(v_declName_4730_);
                        v___x_4752_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_4730_, v___y_4732_);
                        v_a_4753_ = crate::leanh::lean_ctor_get(v___x_4752_, 0);
                        crate::leanh::lean_inc(v_a_4753_);
                        crate::leanh::lean_dec_ref(v___x_4752_);
                        v_ranges_4735_ = v_a_4753_;
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4744_);
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(
    mut v_declName_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4760_ =
        l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(
            v_declName_4756_,
            v___y_4757_,
            v___y_4758_,
        );
    crate::leanh::lean_dec(v___y_4758_);
    crate::leanh::lean_dec_ref(v___y_4757_);
    return v_res_4760_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(
    mut v_as_4761_: *mut crate::leanh::LeanObject,
    mut v_sz_4762_: usize,
    mut v_i_4763_: usize,
    mut v_b_4764_: *mut crate::leanh::LeanObject,
    mut v___y_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4768_: u8 = 0;
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: usize = 0;
    let mut v___x_4777_: usize = 0;
    let mut v_val_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4787_: u8 = 0;
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4768_ = lean_usize_dec_lt(v_i_4763_, v_sz_4762_);
                if v___x_4768_ == 0 {
                    v___x_4769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4769_, 0, v_b_4764_);
                    return v___x_4769_;
                } else {
                    v_a_4770_ = lean_array_uget_borrowed(v_as_4761_, v_i_4763_);
                    v_fst_4771_ = crate::leanh::lean_ctor_get(v_a_4770_, 0);
                    crate::leanh::lean_inc(v_fst_4771_);
                    v___x_4772_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_fst_4771_, v___y_4765_, v___y_4766_);
                    if crate::leanh::lean_obj_tag(v___x_4772_) == 0 {
                        v_a_4773_ = crate::leanh::lean_ctor_get(v___x_4772_, 0);
                        crate::leanh::lean_inc(v_a_4773_);
                        crate::leanh::lean_dec_ref_known(v___x_4772_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4773_) == 1 {
                            v_val_4779_ = crate::leanh::lean_ctor_get(v_a_4773_, 0);
                            crate::leanh::lean_inc(v_val_4779_);
                            crate::leanh::lean_dec_ref_known(v_a_4773_, 1);
                            v_range_4780_ = crate::leanh::lean_ctor_get(v_val_4779_, 0);
                            crate::leanh::lean_inc_ref(v_range_4780_);
                            crate::leanh::lean_dec(v_val_4779_);
                            v_pos_4781_ = crate::leanh::lean_ctor_get(v_range_4780_, 0);
                            crate::leanh::lean_inc_ref(v_pos_4781_);
                            crate::leanh::lean_dec_ref(v_range_4780_);
                            v_line_4782_ = crate::leanh::lean_ctor_get(v_pos_4781_, 0);
                            crate::leanh::lean_inc(v_line_4782_);
                            crate::leanh::lean_dec_ref(v_pos_4781_);
                            crate::leanh::lean_inc(v_fst_4771_);
                            v___x_4783_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_4764_, v_fst_4771_, v_line_4782_);
                            v_a_4775_ = v___x_4783_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4773_);
                            v_a_4775_ = v_b_4764_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4764_);
                        v_a_4784_ = crate::leanh::lean_ctor_get(v___x_4772_, 0);
                        v_isSharedCheck_4791_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4772_)) as u8;
                        if v_isSharedCheck_4791_ == 0 {
                            v___x_4786_ = v___x_4772_;
                            v_isShared_4787_ = v_isSharedCheck_4791_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4784_);
                            crate::leanh::lean_dec(v___x_4772_);
                            v___x_4786_ = crate::leanh::lean_box(0);
                            v_isShared_4787_ = v_isSharedCheck_4791_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4776_ = 1usize;
                v___x_4777_ = lean_usize_add(v_i_4763_, v___x_4776_);
                v_i_4763_ = v___x_4777_;
                v_b_4764_ = v_a_4775_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4787_ == 0 {
                    v___x_4789_ = v___x_4786_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
                    v___x_4789_ = v_reuseFailAlloc_4790_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(
    mut v_as_4792_: *mut crate::leanh::LeanObject,
    mut v_sz_4793_: *mut crate::leanh::LeanObject,
    mut v_i_4794_: *mut crate::leanh::LeanObject,
    mut v_b_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4799_: usize = 0;
    let mut v_i_boxed_4800_: usize = 0;
    let mut v_res_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4799_ = crate::leanh::lean_unbox_usize(v_sz_4793_);
    crate::leanh::lean_dec(v_sz_4793_);
    v_i_boxed_4800_ = crate::leanh::lean_unbox_usize(v_i_4794_);
    crate::leanh::lean_dec(v_i_4794_);
    v_res_4801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_4792_, v_sz_boxed_4799_, v_i_boxed_4800_, v_b_4795_, v___y_4796_, v___y_4797_);
    crate::leanh::lean_dec(v___y_4797_);
    crate::leanh::lean_dec_ref(v___y_4796_);
    crate::leanh::lean_dec_ref(v_as_4792_);
    return v_res_4801_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(
    mut v_x_4802_: *mut crate::leanh::LeanObject,
    mut v_x_4803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4803_) == 0 {
                    return v_x_4802_;
                } else {
                    v_key_4804_ = crate::leanh::lean_ctor_get(v_x_4803_, 0);
                    v_value_4805_ = crate::leanh::lean_ctor_get(v_x_4803_, 1);
                    v_tail_4806_ = crate::leanh::lean_ctor_get(v_x_4803_, 2);
                    crate::leanh::lean_inc(v_value_4805_);
                    crate::leanh::lean_inc(v_key_4804_);
                    v___x_4807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4807_, 0, v_key_4804_);
                    crate::leanh::lean_ctor_set(v___x_4807_, 1, v_value_4805_);
                    v___x_4808_ = lean_array_push(v_x_4802_, v___x_4807_);
                    v_x_4802_ = v___x_4808_;
                    v_x_4803_ = v_tail_4806_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(
    mut v_x_4810_: *mut crate::leanh::LeanObject,
    mut v_x_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4812_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_4810_, v_x_4811_);
    crate::leanh::lean_dec(v_x_4811_);
    return v_res_4812_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(
    mut v_as_4813_: *mut crate::leanh::LeanObject,
    mut v_i_4814_: usize,
    mut v_stop_4815_: usize,
    mut v_b_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4817_: u8 = 0;
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: usize = 0;
    let mut v___x_4821_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4817_ = lean_usize_dec_eq(v_i_4814_, v_stop_4815_);
                if v___x_4817_ == 0 {
                    v___x_4818_ = lean_array_uget_borrowed(v_as_4813_, v_i_4814_);
                    v___x_4819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_b_4816_, v___x_4818_);
                    v___x_4820_ = 1usize;
                    v___x_4821_ = lean_usize_add(v_i_4814_, v___x_4820_);
                    v_i_4814_ = v___x_4821_;
                    v_b_4816_ = v___x_4819_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4816_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(
    mut v_as_4823_: *mut crate::leanh::LeanObject,
    mut v_i_4824_: *mut crate::leanh::LeanObject,
    mut v_stop_4825_: *mut crate::leanh::LeanObject,
    mut v_b_4826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4827_: usize = 0;
    let mut v_stop_boxed_4828_: usize = 0;
    let mut v_res_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4827_ = crate::leanh::lean_unbox_usize(v_i_4824_);
    crate::leanh::lean_dec(v_i_4824_);
    v_stop_boxed_4828_ = crate::leanh::lean_unbox_usize(v_stop_4825_);
    crate::leanh::lean_dec(v_stop_4825_);
    v_res_4829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_4823_, v_i_boxed_4827_, v_stop_boxed_4828_, v_b_4826_);
    crate::leanh::lean_dec_ref(v_as_4823_);
    return v_res_4829_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_sortResults___redArg(
    mut v_results_4830_: *mut crate::leanh::LeanObject,
    mut v_a_4831_: *mut crate::leanh::LeanObject,
    mut v_a_4832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: u8 = 0;
    let mut v_size_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4855_: usize = 0;
    let mut v___x_4856_: usize = 0;
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4861_: u8 = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4870_: u8 = 0;
    let mut v_a_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: u8 = 0;
    let mut v___x_4882_: u8 = 0;
    let mut v___x_4883_: usize = 0;
    let mut v___x_4884_: usize = 0;
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: usize = 0;
    let mut v___x_4887_: usize = 0;
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4849_ = crate::leanh::lean_ctor_get(v_results_4830_, 0);
                v_buckets_4850_ = crate::leanh::lean_ctor_get(v_results_4830_, 1);
                v___x_4851_ = crate::leanh::lean_unsigned_to_nat(0);
                v_key_4852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
                v___x_4879_ = lean_mk_empty_array_with_capacity(v_size_4849_);
                v___x_4880_ = lean_array_get_size(v_buckets_4850_);
                v___x_4881_ = lean_nat_dec_lt(v___x_4851_, v___x_4880_);
                if v___x_4881_ == 0 {
                    v___y_4854_ = v___x_4879_;
                    state = 3;
                    continue;
                } else {
                    v___x_4882_ = lean_nat_dec_le(v___x_4880_, v___x_4880_);
                    if v___x_4882_ == 0 {
                        if v___x_4881_ == 0 {
                            v___y_4854_ = v___x_4879_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4883_ = 0usize;
                            v___x_4884_ = lean_usize_of_nat(v___x_4880_);
                            v___x_4885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_4850_, v___x_4883_, v___x_4884_, v___x_4879_);
                            v___y_4854_ = v___x_4885_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4886_ = 0usize;
                        v___x_4887_ = lean_usize_of_nat(v___x_4880_);
                        v___x_4888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_4850_, v___x_4886_, v___x_4887_, v___x_4879_);
                        v___y_4854_ = v___x_4888_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4840_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v___y_4837_, v___y_4835_, v___y_4838_, v___y_4836_, v___y_4839_);
                crate::leanh::lean_dec(v___y_4839_);
                crate::leanh::lean_dec(v___y_4835_);
                crate::leanh::lean_dec_ref(v___y_4837_);
                v___x_4841_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4841_, 0, v___x_4840_);
                return v___x_4841_;
            }
            2 => {
                v___x_4848_ = lean_nat_dec_le(v___y_4847_, v___y_4843_);
                if v___x_4848_ == 0 {
                    crate::leanh::lean_dec(v___y_4843_);
                    crate::leanh::lean_inc(v___y_4847_);
                    v___y_4835_ = v___y_4844_;
                    v___y_4836_ = v___y_4847_;
                    v___y_4837_ = v___y_4845_;
                    v___y_4838_ = v___y_4846_;
                    v___y_4839_ = v___y_4847_;
                    state = 1;
                    continue;
                } else {
                    v___y_4835_ = v___y_4844_;
                    v___y_4836_ = v___y_4847_;
                    v___y_4837_ = v___y_4845_;
                    v___y_4838_ = v___y_4846_;
                    v___y_4839_ = v___y_4843_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_sz_4855_ = lean_array_size(v___y_4854_);
                v___x_4856_ = 0usize;
                v___x_4857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v___y_4854_, v_sz_4855_, v___x_4856_, v_key_4852_, v_a_4831_, v_a_4832_);
                if crate::leanh::lean_obj_tag(v___x_4857_) == 0 {
                    v_a_4858_ = crate::leanh::lean_ctor_get(v___x_4857_, 0);
                    v_isSharedCheck_4870_ = (!crate::leanh::lean_is_exclusive(v___x_4857_)) as u8;
                    if v_isSharedCheck_4870_ == 0 {
                        v___x_4860_ = v___x_4857_;
                        v_isShared_4861_ = v_isSharedCheck_4870_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4858_);
                        crate::leanh::lean_dec(v___x_4857_);
                        v___x_4860_ = crate::leanh::lean_box(0);
                        v_isShared_4861_ = v_isSharedCheck_4870_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4854_);
                    v_a_4871_ = crate::leanh::lean_ctor_get(v___x_4857_, 0);
                    v_isSharedCheck_4878_ = (!crate::leanh::lean_is_exclusive(v___x_4857_)) as u8;
                    if v_isSharedCheck_4878_ == 0 {
                        v___x_4873_ = v___x_4857_;
                        v_isShared_4874_ = v_isSharedCheck_4878_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4871_);
                        crate::leanh::lean_dec(v___x_4857_);
                        v___x_4873_ = crate::leanh::lean_box(0);
                        v_isShared_4874_ = v_isSharedCheck_4878_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4862_ = lean_array_get_size(v___y_4854_);
                v___x_4863_ = lean_nat_dec_eq(v___x_4862_, v___x_4851_);
                if v___x_4863_ == 0 {
                    crate::leanh::lean_del_object(v___x_4860_);
                    v___x_4864_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4865_ = lean_nat_sub(v___x_4862_, v___x_4864_);
                    v___x_4866_ = lean_nat_dec_le(v___x_4851_, v___x_4865_);
                    if v___x_4866_ == 0 {
                        crate::leanh::lean_inc(v___x_4865_);
                        v___y_4843_ = v___x_4865_;
                        v___y_4844_ = v___x_4862_;
                        v___y_4845_ = v_a_4858_;
                        v___y_4846_ = v___y_4854_;
                        v___y_4847_ = v___x_4865_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4843_ = v___x_4865_;
                        v___y_4844_ = v___x_4862_;
                        v___y_4845_ = v_a_4858_;
                        v___y_4846_ = v___y_4854_;
                        v___y_4847_ = v___x_4851_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4858_);
                    if v_isShared_4861_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4860_, 0, v___y_4854_);
                        v___x_4868_ = v___x_4860_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4869_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___y_4854_);
                        v___x_4868_ = v_reuseFailAlloc_4869_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4868_;
            }
            6 => {
                if v_isShared_4874_ == 0 {
                    v___x_4876_ = v___x_4873_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
                    v___x_4876_ = v_reuseFailAlloc_4877_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(
    mut v_results_4889_: *mut crate::leanh::LeanObject,
    mut v_a_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4893_ =
        l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_4889_, v_a_4890_, v_a_4891_);
    crate::leanh::lean_dec(v_a_4891_);
    crate::leanh::lean_dec_ref(v_a_4890_);
    crate::leanh::lean_dec_ref(v_results_4889_);
    return v_res_4893_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_sortResults(
    mut v_00_u03b1_4894_: *mut crate::leanh::LeanObject,
    mut v_results_4895_: *mut crate::leanh::LeanObject,
    mut v_a_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4899_ =
        l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_4895_, v_a_4896_, v_a_4897_);
    return v___x_4899_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_sortResults___boxed(
    mut v_00_u03b1_4900_: *mut crate::leanh::LeanObject,
    mut v_results_4901_: *mut crate::leanh::LeanObject,
    mut v_a_4902_: *mut crate::leanh::LeanObject,
    mut v_a_4903_: *mut crate::leanh::LeanObject,
    mut v_a_4904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4905_ = l_Lean_Linter_EnvLinter_sortResults(
        v_00_u03b1_4900_,
        v_results_4901_,
        v_a_4902_,
        v_a_4903_,
    );
    crate::leanh::lean_dec(v_a_4903_);
    crate::leanh::lean_dec_ref(v_a_4902_);
    crate::leanh::lean_dec_ref(v_results_4901_);
    return v_res_4905_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(
    mut v_declName_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
    mut v___y_4908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4910_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_4906_, v___y_4908_);
    return v___x_4910_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(
    mut v_declName_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4915_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(v_declName_4911_, v___y_4912_, v___y_4913_);
    crate::leanh::lean_dec(v___y_4913_);
    crate::leanh::lean_dec_ref(v___y_4912_);
    return v_res_4915_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(
    mut v_declName_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_4916_, v___y_4918_);
    return v___x_4920_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(
    mut v_declName_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
    mut v___y_4924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4925_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(v_declName_4921_, v___y_4922_, v___y_4923_);
    crate::leanh::lean_dec(v___y_4923_);
    crate::leanh::lean_dec_ref(v___y_4922_);
    return v_res_4925_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(
    mut v_00_u03b1_4926_: *mut crate::leanh::LeanObject,
    mut v_as_4927_: *mut crate::leanh::LeanObject,
    mut v_sz_4928_: usize,
    mut v_i_4929_: usize,
    mut v_b_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_4927_, v_sz_4928_, v_i_4929_, v_b_4930_, v___y_4931_, v___y_4932_);
    return v___x_4934_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(
    mut v_00_u03b1_4935_: *mut crate::leanh::LeanObject,
    mut v_as_4936_: *mut crate::leanh::LeanObject,
    mut v_sz_4937_: *mut crate::leanh::LeanObject,
    mut v_i_4938_: *mut crate::leanh::LeanObject,
    mut v_b_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4943_: usize = 0;
    let mut v_i_boxed_4944_: usize = 0;
    let mut v_res_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4943_ = crate::leanh::lean_unbox_usize(v_sz_4937_);
    crate::leanh::lean_dec(v_sz_4937_);
    v_i_boxed_4944_ = crate::leanh::lean_unbox_usize(v_i_4938_);
    crate::leanh::lean_dec(v_i_4938_);
    v_res_4945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(v_00_u03b1_4935_, v_as_4936_, v_sz_boxed_4943_, v_i_boxed_4944_, v_b_4939_, v___y_4940_, v___y_4941_);
    crate::leanh::lean_dec(v___y_4941_);
    crate::leanh::lean_dec_ref(v___y_4940_);
    crate::leanh::lean_dec_ref(v_as_4936_);
    return v_res_4945_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(
    mut v_00_u03b2_4946_: *mut crate::leanh::LeanObject,
    mut v_m_4947_: *mut crate::leanh::LeanObject,
    mut v_a_4948_: *mut crate::leanh::LeanObject,
    mut v_fallback_4949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_4947_, v_a_4948_, v_fallback_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(
    mut v_00_u03b2_4951_: *mut crate::leanh::LeanObject,
    mut v_m_4952_: *mut crate::leanh::LeanObject,
    mut v_a_4953_: *mut crate::leanh::LeanObject,
    mut v_fallback_4954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(v_00_u03b2_4951_, v_m_4952_, v_a_4953_, v_fallback_4954_);
    crate::leanh::lean_dec(v_fallback_4954_);
    crate::leanh::lean_dec(v_a_4953_);
    crate::leanh::lean_dec_ref(v_m_4952_);
    return v_res_4955_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(
    mut v_00_u03b1_4956_: *mut crate::leanh::LeanObject,
    mut v_a_4957_: *mut crate::leanh::LeanObject,
    mut v_n_4958_: *mut crate::leanh::LeanObject,
    mut v_as_4959_: *mut crate::leanh::LeanObject,
    mut v_lo_4960_: *mut crate::leanh::LeanObject,
    mut v_hi_4961_: *mut crate::leanh::LeanObject,
    mut v_w_4962_: *mut crate::leanh::LeanObject,
    mut v_hlo_4963_: *mut crate::leanh::LeanObject,
    mut v_hhi_4964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_4957_, v_n_4958_, v_as_4959_, v_lo_4960_, v_hi_4961_);
    return v___x_4965_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(
    mut v_00_u03b1_4966_: *mut crate::leanh::LeanObject,
    mut v_a_4967_: *mut crate::leanh::LeanObject,
    mut v_n_4968_: *mut crate::leanh::LeanObject,
    mut v_as_4969_: *mut crate::leanh::LeanObject,
    mut v_lo_4970_: *mut crate::leanh::LeanObject,
    mut v_hi_4971_: *mut crate::leanh::LeanObject,
    mut v_w_4972_: *mut crate::leanh::LeanObject,
    mut v_hlo_4973_: *mut crate::leanh::LeanObject,
    mut v_hhi_4974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4975_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(v_00_u03b1_4966_, v_a_4967_, v_n_4968_, v_as_4969_, v_lo_4970_, v_hi_4971_, v_w_4972_, v_hlo_4973_, v_hhi_4974_);
    crate::leanh::lean_dec(v_hi_4971_);
    crate::leanh::lean_dec(v_n_4968_);
    crate::leanh::lean_dec_ref(v_a_4967_);
    return v_res_4975_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(
    mut v_00_u03b1_4976_: *mut crate::leanh::LeanObject,
    mut v_x_4977_: *mut crate::leanh::LeanObject,
    mut v_x_4978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4979_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_4977_, v_x_4978_);
    return v___x_4979_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(
    mut v_00_u03b1_4980_: *mut crate::leanh::LeanObject,
    mut v_x_4981_: *mut crate::leanh::LeanObject,
    mut v_x_4982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4983_ =
        l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(
            v_00_u03b1_4980_,
            v_x_4981_,
            v_x_4982_,
        );
    crate::leanh::lean_dec(v_x_4982_);
    return v_res_4983_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(
    mut v_00_u03b1_4984_: *mut crate::leanh::LeanObject,
    mut v_as_4985_: *mut crate::leanh::LeanObject,
    mut v_i_4986_: usize,
    mut v_stop_4987_: usize,
    mut v_b_4988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_4985_, v_i_4986_, v_stop_4987_, v_b_4988_);
    return v___x_4989_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(
    mut v_00_u03b1_4990_: *mut crate::leanh::LeanObject,
    mut v_as_4991_: *mut crate::leanh::LeanObject,
    mut v_i_4992_: *mut crate::leanh::LeanObject,
    mut v_stop_4993_: *mut crate::leanh::LeanObject,
    mut v_b_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4995_: usize = 0;
    let mut v_stop_boxed_4996_: usize = 0;
    let mut v_res_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4995_ = crate::leanh::lean_unbox_usize(v_i_4992_);
    crate::leanh::lean_dec(v_i_4992_);
    v_stop_boxed_4996_ = crate::leanh::lean_unbox_usize(v_stop_4993_);
    crate::leanh::lean_dec(v_stop_4993_);
    v_res_4997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(v_00_u03b1_4990_, v_as_4991_, v_i_boxed_4995_, v_stop_boxed_4996_, v_b_4994_);
    crate::leanh::lean_dec_ref(v_as_4991_);
    return v_res_4997_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(
    mut v_00_u03b2_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
    mut v_fallback_5000_: *mut crate::leanh::LeanObject,
    mut v_x_5001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5002_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_4999_, v_fallback_5000_, v_x_5001_);
    return v___x_5002_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(
    mut v_00_u03b2_5003_: *mut crate::leanh::LeanObject,
    mut v_a_5004_: *mut crate::leanh::LeanObject,
    mut v_fallback_5005_: *mut crate::leanh::LeanObject,
    mut v_x_5006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5007_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(v_00_u03b2_5003_, v_a_5004_, v_fallback_5005_, v_x_5006_);
    crate::leanh::lean_dec(v_x_5006_);
    crate::leanh::lean_dec(v_fallback_5005_);
    crate::leanh::lean_dec(v_a_5004_);
    return v_res_5007_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(
    mut v_00_u03b1_5008_: *mut crate::leanh::LeanObject,
    mut v_a_5009_: *mut crate::leanh::LeanObject,
    mut v_n_5010_: *mut crate::leanh::LeanObject,
    mut v_lo_5011_: *mut crate::leanh::LeanObject,
    mut v_hi_5012_: *mut crate::leanh::LeanObject,
    mut v_hhi_5013_: *mut crate::leanh::LeanObject,
    mut v_pivot_5014_: *mut crate::leanh::LeanObject,
    mut v_as_5015_: *mut crate::leanh::LeanObject,
    mut v_i_5016_: *mut crate::leanh::LeanObject,
    mut v_k_5017_: *mut crate::leanh::LeanObject,
    mut v_ilo_5018_: *mut crate::leanh::LeanObject,
    mut v_ik_5019_: *mut crate::leanh::LeanObject,
    mut v_w_5020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_5009_, v_hi_5012_, v_pivot_5014_, v_as_5015_, v_i_5016_, v_k_5017_);
    return v___x_5021_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(
    mut v_00_u03b1_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_n_5024_: *mut crate::leanh::LeanObject,
    mut v_lo_5025_: *mut crate::leanh::LeanObject,
    mut v_hi_5026_: *mut crate::leanh::LeanObject,
    mut v_hhi_5027_: *mut crate::leanh::LeanObject,
    mut v_pivot_5028_: *mut crate::leanh::LeanObject,
    mut v_as_5029_: *mut crate::leanh::LeanObject,
    mut v_i_5030_: *mut crate::leanh::LeanObject,
    mut v_k_5031_: *mut crate::leanh::LeanObject,
    mut v_ilo_5032_: *mut crate::leanh::LeanObject,
    mut v_ik_5033_: *mut crate::leanh::LeanObject,
    mut v_w_5034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(v_00_u03b1_5022_, v_a_5023_, v_n_5024_, v_lo_5025_, v_hi_5026_, v_hhi_5027_, v_pivot_5028_, v_as_5029_, v_i_5030_, v_k_5031_, v_ilo_5032_, v_ik_5033_, v_w_5034_);
    crate::leanh::lean_dec_ref(v_pivot_5028_);
    crate::leanh::lean_dec(v_hi_5026_);
    crate::leanh::lean_dec(v_lo_5025_);
    crate::leanh::lean_dec(v_n_5024_);
    crate::leanh::lean_dec_ref(v_a_5023_);
    return v_res_5035_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5036_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
    v___x_5037_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5038_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5038_, 0, v___x_5037_);
    crate::leanh::lean_ctor_set(v___x_5038_, 1, v___x_5037_);
    crate::leanh::lean_ctor_set(v___x_5038_, 2, v___x_5037_);
    crate::leanh::lean_ctor_set(v___x_5038_, 3, v___x_5037_);
    crate::leanh::lean_ctor_set(v___x_5038_, 4, v___x_5036_);
    crate::leanh::lean_ctor_set(v___x_5038_, 5, v___x_5036_);
    crate::leanh::lean_ctor_set(v___x_5038_, 6, v___x_5036_);
    crate::leanh::lean_ctor_set(v___x_5038_, 7, v___x_5036_);
    crate::leanh::lean_ctor_set(v___x_5038_, 8, v___x_5036_);
    crate::leanh::lean_ctor_set(v___x_5038_, 9, v___x_5036_);
    return v___x_5038_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5039_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5040_ = lean_mk_empty_array_with_capacity(v___x_5039_);
    v___x_5041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5041_, 0, v___x_5040_);
    return v___x_5041_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5042_: usize = 0;
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = 5usize;
    v___x_5043_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5044_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5045_ = lean_mk_empty_array_with_capacity(v___x_5044_);
    v___x_5046_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1);
    v___x_5047_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5047_, 0, v___x_5046_);
    crate::leanh::lean_ctor_set(v___x_5047_, 1, v___x_5045_);
    crate::leanh::lean_ctor_set(v___x_5047_, 2, v___x_5043_);
    crate::leanh::lean_ctor_set(v___x_5047_, 3, v___x_5043_);
    crate::leanh::lean_ctor_set_usize(v___x_5047_, 4, v___x_5042_);
    return v___x_5047_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5048_ = crate::leanh::lean_box(1);
    v___x_5049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2);
    v___x_5050_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
    v___x_5051_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5051_, 0, v___x_5050_);
    crate::leanh::lean_ctor_set(v___x_5051_, 1, v___x_5049_);
    crate::leanh::lean_ctor_set(v___x_5051_, 2, v___x_5048_);
    return v___x_5051_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(
    mut v_msgData_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5056_ = lean_st_ref_get(v___y_5054_);
    v_env_5057_ = crate::leanh::lean_ctor_get(v___x_5056_, 0);
    crate::leanh::lean_inc_ref(v_env_5057_);
    crate::leanh::lean_dec(v___x_5056_);
    v_options_5058_ = crate::leanh::lean_ctor_get(v___y_5053_, 2);
    v___x_5059_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
    v___x_5060_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
    crate::leanh::lean_inc_ref(v_options_5058_);
    v___x_5061_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5061_, 0, v_env_5057_);
    crate::leanh::lean_ctor_set(v___x_5061_, 1, v___x_5059_);
    crate::leanh::lean_ctor_set(v___x_5061_, 2, v___x_5060_);
    crate::leanh::lean_ctor_set(v___x_5061_, 3, v_options_5058_);
    v___x_5062_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5062_, 0, v___x_5061_);
    crate::leanh::lean_ctor_set(v___x_5062_, 1, v_msgData_5052_);
    v___x_5063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5063_, 0, v___x_5062_);
    return v___x_5063_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(
    mut v_msgData_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5068_ =
        l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(
            v_msgData_5064_,
            v___y_5065_,
            v___y_5066_,
        );
    crate::leanh::lean_dec(v___y_5066_);
    crate::leanh::lean_dec_ref(v___y_5065_);
    return v_res_5068_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(
    mut v_a_5069_: *mut crate::leanh::LeanObject,
    mut v_a_5070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5076_: u8 = 0;
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5082_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5069_) == 0 {
                    v___x_5071_ = l_List_reverse___redArg(v_a_5070_);
                    return v___x_5071_;
                } else {
                    v_head_5072_ = crate::leanh::lean_ctor_get(v_a_5069_, 0);
                    v_tail_5073_ = crate::leanh::lean_ctor_get(v_a_5069_, 1);
                    v_isSharedCheck_5082_ = (!crate::leanh::lean_is_exclusive(v_a_5069_)) as u8;
                    if v_isSharedCheck_5082_ == 0 {
                        v___x_5075_ = v_a_5069_;
                        v_isShared_5076_ = v_isSharedCheck_5082_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5073_);
                        crate::leanh::lean_inc(v_head_5072_);
                        crate::leanh::lean_dec(v_a_5069_);
                        v___x_5075_ = crate::leanh::lean_box(0);
                        v_isShared_5076_ = v_isSharedCheck_5082_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5077_ = l_Lean_mkLevelParam(v_head_5072_);
                if v_isShared_5076_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5075_, 1, v_a_5070_);
                    crate::leanh::lean_ctor_set(v___x_5075_, 0, v___x_5077_);
                    v___x_5079_ = v___x_5075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5081_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5081_, 1, v_a_5070_);
                    v___x_5079_ = v_reuseFailAlloc_5081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5069_ = v_tail_5073_;
                v_a_5070_ = v___x_5079_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(
    mut v_msg_5083_: *mut crate::leanh::LeanObject,
    mut v___y_5084_: *mut crate::leanh::LeanObject,
    mut v___y_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5087_ = crate::leanh::lean_ctor_get(v___y_5084_, 5);
                v___x_5088_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msg_5083_, v___y_5084_, v___y_5085_);
                v_a_5089_ = crate::leanh::lean_ctor_get(v___x_5088_, 0);
                v_isSharedCheck_5097_ = (!crate::leanh::lean_is_exclusive(v___x_5088_)) as u8;
                if v_isSharedCheck_5097_ == 0 {
                    v___x_5091_ = v___x_5088_;
                    v_isShared_5092_ = v_isSharedCheck_5097_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5089_);
                    crate::leanh::lean_dec(v___x_5088_);
                    v___x_5091_ = crate::leanh::lean_box(0);
                    v_isShared_5092_ = v_isSharedCheck_5097_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5087_);
                v___x_5093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5093_, 0, v_ref_5087_);
                crate::leanh::lean_ctor_set(v___x_5093_, 1, v_a_5089_);
                if v_isShared_5092_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5091_, 1);
                    crate::leanh::lean_ctor_set(v___x_5091_, 0, v___x_5093_);
                    v___x_5095_ = v___x_5091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5096_, 0, v___x_5093_);
                    v___x_5095_ = v_reuseFailAlloc_5096_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_msg_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
    mut v___y_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5102_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_5098_, v___y_5099_, v___y_5100_);
    crate::leanh::lean_dec(v___y_5100_);
    crate::leanh::lean_dec_ref(v___y_5099_);
    return v_res_5102_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_ref_5103_: *mut crate::leanh::LeanObject,
    mut v_msg_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5120_: u8 = 0;
    let mut v_cancelTk_x3f_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5122_: u8 = 0;
    let mut v_inheritedTraceOptions_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5108_ = crate::leanh::lean_ctor_get(v___y_5105_, 0);
    v_fileMap_5109_ = crate::leanh::lean_ctor_get(v___y_5105_, 1);
    v_options_5110_ = crate::leanh::lean_ctor_get(v___y_5105_, 2);
    v_currRecDepth_5111_ = crate::leanh::lean_ctor_get(v___y_5105_, 3);
    v_maxRecDepth_5112_ = crate::leanh::lean_ctor_get(v___y_5105_, 4);
    v_ref_5113_ = crate::leanh::lean_ctor_get(v___y_5105_, 5);
    v_currNamespace_5114_ = crate::leanh::lean_ctor_get(v___y_5105_, 6);
    v_openDecls_5115_ = crate::leanh::lean_ctor_get(v___y_5105_, 7);
    v_initHeartbeats_5116_ = crate::leanh::lean_ctor_get(v___y_5105_, 8);
    v_maxHeartbeats_5117_ = crate::leanh::lean_ctor_get(v___y_5105_, 9);
    v_quotContext_5118_ = crate::leanh::lean_ctor_get(v___y_5105_, 10);
    v_currMacroScope_5119_ = crate::leanh::lean_ctor_get(v___y_5105_, 11);
    v_diag_5120_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5105_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5121_ = crate::leanh::lean_ctor_get(v___y_5105_, 12);
    v_suppressElabErrors_5122_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5105_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5123_ = crate::leanh::lean_ctor_get(v___y_5105_, 13);
    v_ref_5124_ = l_Lean_replaceRef(v_ref_5103_, v_ref_5113_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5123_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5121_);
    crate::leanh::lean_inc(v_currMacroScope_5119_);
    crate::leanh::lean_inc(v_quotContext_5118_);
    crate::leanh::lean_inc(v_maxHeartbeats_5117_);
    crate::leanh::lean_inc(v_initHeartbeats_5116_);
    crate::leanh::lean_inc(v_openDecls_5115_);
    crate::leanh::lean_inc(v_currNamespace_5114_);
    crate::leanh::lean_inc(v_maxRecDepth_5112_);
    crate::leanh::lean_inc(v_currRecDepth_5111_);
    crate::leanh::lean_inc_ref(v_options_5110_);
    crate::leanh::lean_inc_ref(v_fileMap_5109_);
    crate::leanh::lean_inc_ref(v_fileName_5108_);
    v___x_5125_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5125_, 0, v_fileName_5108_);
    crate::leanh::lean_ctor_set(v___x_5125_, 1, v_fileMap_5109_);
    crate::leanh::lean_ctor_set(v___x_5125_, 2, v_options_5110_);
    crate::leanh::lean_ctor_set(v___x_5125_, 3, v_currRecDepth_5111_);
    crate::leanh::lean_ctor_set(v___x_5125_, 4, v_maxRecDepth_5112_);
    crate::leanh::lean_ctor_set(v___x_5125_, 5, v_ref_5124_);
    crate::leanh::lean_ctor_set(v___x_5125_, 6, v_currNamespace_5114_);
    crate::leanh::lean_ctor_set(v___x_5125_, 7, v_openDecls_5115_);
    crate::leanh::lean_ctor_set(v___x_5125_, 8, v_initHeartbeats_5116_);
    crate::leanh::lean_ctor_set(v___x_5125_, 9, v_maxHeartbeats_5117_);
    crate::leanh::lean_ctor_set(v___x_5125_, 10, v_quotContext_5118_);
    crate::leanh::lean_ctor_set(v___x_5125_, 11, v_currMacroScope_5119_);
    crate::leanh::lean_ctor_set(v___x_5125_, 12, v_cancelTk_x3f_5121_);
    crate::leanh::lean_ctor_set(v___x_5125_, 13, v_inheritedTraceOptions_5123_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5125_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5120_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5125_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5122_,
    );
    v___x_5126_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_5104_, v___x_5125_, v___y_5106_);
    crate::leanh::lean_dec_ref_known(v___x_5125_, 14);
    return v___x_5126_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_ref_5127_: *mut crate::leanh::LeanObject,
    mut v_msg_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
    mut v___y_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5132_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_5127_, v_msg_5128_, v___y_5129_, v___y_5130_);
    crate::leanh::lean_dec(v___y_5130_);
    crate::leanh::lean_dec_ref(v___y_5129_);
    crate::leanh::lean_dec(v_ref_5127_);
    return v_res_5132_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5134_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0;
    v___x_5135_ = l_Lean_stringToMessageData(v___x_5134_);
    return v___x_5135_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5137_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2;
    v___x_5138_ = l_Lean_stringToMessageData(v___x_5137_);
    return v___x_5138_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5140_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4;
    v___x_5141_ = l_Lean_stringToMessageData(v___x_5140_);
    return v___x_5141_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5143_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_5144_ = l_Lean_stringToMessageData(v___x_5143_);
    return v___x_5144_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5146_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_5147_ = l_Lean_stringToMessageData(v___x_5146_);
    return v___x_5147_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5149_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_5150_ = l_Lean_stringToMessageData(v___x_5149_);
    return v___x_5150_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5152_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_5153_ = l_Lean_stringToMessageData(v___x_5152_);
    return v___x_5153_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(
    mut v_msg_5154_: *mut crate::leanh::LeanObject,
    mut v_declHint_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: u8 = 0;
    let mut v_isExporting_5161_: u8 = 0;
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: u8 = 0;
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5183_: u8 = 0;
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: u8 = 0;
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5158_ = lean_st_ref_get(v___y_5156_);
                v_env_5159_ = crate::leanh::lean_ctor_get(v___x_5158_, 0);
                crate::leanh::lean_inc_ref(v_env_5159_);
                crate::leanh::lean_dec(v___x_5158_);
                v___x_5160_ = l_Lean_Name_isAnonymous(v_declHint_5155_);
                if v___x_5160_ == 0 {
                    v_isExporting_5161_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_5159_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5161_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_5159_);
                        crate::leanh::lean_dec(v_declHint_5155_);
                        v___x_5162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5162_, 0, v_msg_5154_);
                        return v___x_5162_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_5159_);
                        v___x_5163_ = l_Lean_Environment_setExporting(v_env_5159_, v___x_5160_);
                        crate::leanh::lean_inc(v_declHint_5155_);
                        crate::leanh::lean_inc_ref(v___x_5163_);
                        v___x_5164_ = l_Lean_Environment_contains(
                            v___x_5163_,
                            v_declHint_5155_,
                            v_isExporting_5161_,
                        );
                        if v___x_5164_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5163_);
                            crate::leanh::lean_dec_ref(v_env_5159_);
                            crate::leanh::lean_dec(v_declHint_5155_);
                            v___x_5165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5165_, 0, v_msg_5154_);
                            return v___x_5165_;
                        } else {
                            v___x_5166_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
                            v___x_5167_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
                            v___x_5168_ = l_Lean_Options_empty;
                            v___x_5169_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5169_, 0, v___x_5163_);
                            crate::leanh::lean_ctor_set(v___x_5169_, 1, v___x_5166_);
                            crate::leanh::lean_ctor_set(v___x_5169_, 2, v___x_5167_);
                            crate::leanh::lean_ctor_set(v___x_5169_, 3, v___x_5168_);
                            crate::leanh::lean_inc(v_declHint_5155_);
                            v___x_5170_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5155_, v___x_5160_);
                            v_c_5171_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_5171_, 0, v___x_5169_);
                            crate::leanh::lean_ctor_set(v_c_5171_, 1, v___x_5170_);
                            v___x_5172_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5159_,
                                v_declHint_5155_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5172_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_5159_);
                                crate::leanh::lean_dec(v_declHint_5155_);
                                v___x_5173_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
                                v___x_5174_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5174_, 0, v___x_5173_);
                                crate::leanh::lean_ctor_set(v___x_5174_, 1, v_c_5171_);
                                v___x_5175_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
                                v___x_5176_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5176_, 0, v___x_5174_);
                                crate::leanh::lean_ctor_set(v___x_5176_, 1, v___x_5175_);
                                v___x_5177_ = l_Lean_MessageData_note(v___x_5176_);
                                v___x_5178_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5178_, 0, v_msg_5154_);
                                crate::leanh::lean_ctor_set(v___x_5178_, 1, v___x_5177_);
                                v___x_5179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5179_, 0, v___x_5178_);
                                return v___x_5179_;
                            } else {
                                v_val_5180_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                                v_isSharedCheck_5215_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5172_)) as u8;
                                if v_isSharedCheck_5215_ == 0 {
                                    v___x_5182_ = v___x_5172_;
                                    v_isShared_5183_ = v_isSharedCheck_5215_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_5180_);
                                    crate::leanh::lean_dec(v___x_5172_);
                                    v___x_5182_ = crate::leanh::lean_box(0);
                                    v_isShared_5183_ = v_isSharedCheck_5215_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5159_);
                    crate::leanh::lean_dec(v_declHint_5155_);
                    v___x_5216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5216_, 0, v_msg_5154_);
                    return v___x_5216_;
                }
            }
            1 => {
                v___x_5184_ = crate::leanh::lean_box(0);
                v___x_5185_ = l_Lean_Environment_header(v_env_5159_);
                crate::leanh::lean_dec_ref(v_env_5159_);
                v___x_5186_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5185_);
                v_mod_5187_ = lean_array_get(v___x_5184_, v___x_5186_, v_val_5180_);
                crate::leanh::lean_dec(v_val_5180_);
                crate::leanh::lean_dec_ref(v___x_5186_);
                v___x_5188_ = l_Lean_isPrivateName(v_declHint_5155_);
                crate::leanh::lean_dec(v_declHint_5155_);
                if v___x_5188_ == 0 {
                    v___x_5189_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
                    v___x_5190_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5190_, 0, v___x_5189_);
                    crate::leanh::lean_ctor_set(v___x_5190_, 1, v_c_5171_);
                    v___x_5191_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_5192_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5192_, 0, v___x_5190_);
                    crate::leanh::lean_ctor_set(v___x_5192_, 1, v___x_5191_);
                    v___x_5193_ = l_Lean_MessageData_ofName(v_mod_5187_);
                    v___x_5194_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5194_, 0, v___x_5192_);
                    crate::leanh::lean_ctor_set(v___x_5194_, 1, v___x_5193_);
                    v___x_5195_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
                    v___x_5196_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5196_, 0, v___x_5194_);
                    crate::leanh::lean_ctor_set(v___x_5196_, 1, v___x_5195_);
                    v___x_5197_ = l_Lean_MessageData_note(v___x_5196_);
                    v___x_5198_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5198_, 0, v_msg_5154_);
                    crate::leanh::lean_ctor_set(v___x_5198_, 1, v___x_5197_);
                    if v_isShared_5183_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5182_, 0);
                        crate::leanh::lean_ctor_set(v___x_5182_, 0, v___x_5198_);
                        v___x_5200_ = v___x_5182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
                        v___x_5200_ = v_reuseFailAlloc_5201_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5202_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
                    v___x_5203_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5203_, 0, v___x_5202_);
                    crate::leanh::lean_ctor_set(v___x_5203_, 1, v_c_5171_);
                    v___x_5204_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_5205_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5205_, 0, v___x_5203_);
                    crate::leanh::lean_ctor_set(v___x_5205_, 1, v___x_5204_);
                    v___x_5206_ = l_Lean_MessageData_ofName(v_mod_5187_);
                    v___x_5207_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5207_, 0, v___x_5205_);
                    crate::leanh::lean_ctor_set(v___x_5207_, 1, v___x_5206_);
                    v___x_5208_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_5209_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5209_, 0, v___x_5207_);
                    crate::leanh::lean_ctor_set(v___x_5209_, 1, v___x_5208_);
                    v___x_5210_ = l_Lean_MessageData_note(v___x_5209_);
                    v___x_5211_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5211_, 0, v_msg_5154_);
                    crate::leanh::lean_ctor_set(v___x_5211_, 1, v___x_5210_);
                    if v_isShared_5183_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5182_, 0);
                        crate::leanh::lean_ctor_set(v___x_5182_, 0, v___x_5211_);
                        v___x_5213_ = v___x_5182_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v___x_5211_);
                        v___x_5213_ = v_reuseFailAlloc_5214_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5200_;
            }
            3 => {
                return v___x_5213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_msg_5217_: *mut crate::leanh::LeanObject,
    mut v_declHint_5218_: *mut crate::leanh::LeanObject,
    mut v___y_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_5217_, v_declHint_5218_, v___y_5219_);
    crate::leanh::lean_dec(v___y_5219_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(
    mut v_msg_5222_: *mut crate::leanh::LeanObject,
    mut v_declHint_5223_: *mut crate::leanh::LeanObject,
    mut v___y_5224_: *mut crate::leanh::LeanObject,
    mut v___y_5225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5231_: u8 = 0;
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_5222_, v_declHint_5223_, v___y_5225_);
                v_a_5228_ = crate::leanh::lean_ctor_get(v___x_5227_, 0);
                v_isSharedCheck_5237_ = (!crate::leanh::lean_is_exclusive(v___x_5227_)) as u8;
                if v_isSharedCheck_5237_ == 0 {
                    v___x_5230_ = v___x_5227_;
                    v_isShared_5231_ = v_isSharedCheck_5237_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5228_);
                    crate::leanh::lean_dec(v___x_5227_);
                    v___x_5230_ = crate::leanh::lean_box(0);
                    v_isShared_5231_ = v_isSharedCheck_5237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5232_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5233_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5233_, 0, v___x_5232_);
                crate::leanh::lean_ctor_set(v___x_5233_, 1, v_a_5228_);
                if v_isShared_5231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5230_, 0, v___x_5233_);
                    v___x_5235_ = v___x_5230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___x_5233_);
                    v___x_5235_ = v_reuseFailAlloc_5236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(
    mut v_msg_5238_: *mut crate::leanh::LeanObject,
    mut v_declHint_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5243_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_5238_, v_declHint_5239_, v___y_5240_, v___y_5241_);
    crate::leanh::lean_dec(v___y_5241_);
    crate::leanh::lean_dec_ref(v___y_5240_);
    return v_res_5243_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_ref_5244_: *mut crate::leanh::LeanObject,
    mut v_msg_5245_: *mut crate::leanh::LeanObject,
    mut v_declHint_5246_: *mut crate::leanh::LeanObject,
    mut v___y_5247_: *mut crate::leanh::LeanObject,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5250_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_5245_, v_declHint_5246_, v___y_5247_, v___y_5248_);
    v_a_5251_ = crate::leanh::lean_ctor_get(v___x_5250_, 0);
    crate::leanh::lean_inc(v_a_5251_);
    crate::leanh::lean_dec_ref(v___x_5250_);
    v___x_5252_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_5244_, v_a_5251_, v___y_5247_, v___y_5248_);
    return v___x_5252_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_5253_: *mut crate::leanh::LeanObject,
    mut v_msg_5254_: *mut crate::leanh::LeanObject,
    mut v_declHint_5255_: *mut crate::leanh::LeanObject,
    mut v___y_5256_: *mut crate::leanh::LeanObject,
    mut v___y_5257_: *mut crate::leanh::LeanObject,
    mut v___y_5258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5259_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_5253_, v_msg_5254_, v_declHint_5255_, v___y_5256_, v___y_5257_);
    crate::leanh::lean_dec(v___y_5257_);
    crate::leanh::lean_dec_ref(v___y_5256_);
    crate::leanh::lean_dec(v_ref_5253_);
    return v_res_5259_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5261_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0;
    v___x_5262_ = l_Lean_stringToMessageData(v___x_5261_);
    return v___x_5262_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5264_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2;
    v___x_5265_ = l_Lean_stringToMessageData(v___x_5264_);
    return v___x_5265_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_ref_5266_: *mut crate::leanh::LeanObject,
    mut v_constName_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: u8 = 0;
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5271_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
    v___x_5272_ = 0;
    crate::leanh::lean_inc(v_constName_5267_);
    v___x_5273_ = l_Lean_MessageData_ofConstName(v_constName_5267_, v___x_5272_);
    v___x_5274_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5274_, 0, v___x_5271_);
    crate::leanh::lean_ctor_set(v___x_5274_, 1, v___x_5273_);
    v___x_5275_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3);
    v___x_5276_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5276_, 0, v___x_5274_);
    crate::leanh::lean_ctor_set(v___x_5276_, 1, v___x_5275_);
    v___x_5277_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_5266_, v___x_5276_, v_constName_5267_, v___y_5268_, v___y_5269_);
    return v___x_5277_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_ref_5278_: *mut crate::leanh::LeanObject,
    mut v_constName_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5283_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_5278_, v_constName_5279_, v___y_5280_, v___y_5281_);
    crate::leanh::lean_dec(v___y_5281_);
    crate::leanh::lean_dec_ref(v___y_5280_);
    crate::leanh::lean_dec(v_ref_5278_);
    return v_res_5283_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(
    mut v_constName_5284_: *mut crate::leanh::LeanObject,
    mut v___y_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5288_ = crate::leanh::lean_ctor_get(v___y_5285_, 5);
    v___x_5289_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_5288_, v_constName_5284_, v___y_5285_, v___y_5286_);
    return v___x_5289_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_constName_5290_: *mut crate::leanh::LeanObject,
    mut v___y_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5294_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_5290_, v___y_5291_, v___y_5292_);
    crate::leanh::lean_dec(v___y_5292_);
    crate::leanh::lean_dec_ref(v___y_5291_);
    return v_res_5294_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(
    mut v_constName_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: u8 = 0;
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5307_: u8 = 0;
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5299_ = lean_st_ref_get(v___y_5297_);
                v_env_5300_ = crate::leanh::lean_ctor_get(v___x_5299_, 0);
                crate::leanh::lean_inc_ref(v_env_5300_);
                crate::leanh::lean_dec(v___x_5299_);
                v___x_5301_ = 0;
                crate::leanh::lean_inc(v_constName_5295_);
                v___x_5302_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_5300_,
                    v_constName_5295_,
                    v___x_5301_,
                );
                if crate::leanh::lean_obj_tag(v___x_5302_) == 0 {
                    v___x_5303_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_5295_, v___y_5296_, v___y_5297_);
                    return v___x_5303_;
                } else {
                    crate::leanh::lean_dec(v_constName_5295_);
                    v_val_5304_ = crate::leanh::lean_ctor_get(v___x_5302_, 0);
                    v_isSharedCheck_5311_ = (!crate::leanh::lean_is_exclusive(v___x_5302_)) as u8;
                    if v_isSharedCheck_5311_ == 0 {
                        v___x_5306_ = v___x_5302_;
                        v_isShared_5307_ = v_isSharedCheck_5311_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5304_);
                        crate::leanh::lean_dec(v___x_5302_);
                        v___x_5306_ = crate::leanh::lean_box(0);
                        v_isShared_5307_ = v_isSharedCheck_5311_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5307_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5306_, 0);
                    v___x_5309_ = v___x_5306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5310_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_val_5304_);
                    v___x_5309_ = v_reuseFailAlloc_5310_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(
    mut v_constName_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5316_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_5312_, v___y_5313_, v___y_5314_);
    crate::leanh::lean_dec(v___y_5314_);
    crate::leanh::lean_dec_ref(v___y_5313_);
    return v_res_5316_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(
    mut v_constName_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
    mut v___y_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5325_: u8 = 0;
    let mut v_levelParams_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut v_a_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5337_: u8 = 0;
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_5317_);
                v___x_5321_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_5317_, v___y_5318_, v___y_5319_);
                if crate::leanh::lean_obj_tag(v___x_5321_) == 0 {
                    v_a_5322_ = crate::leanh::lean_ctor_get(v___x_5321_, 0);
                    v_isSharedCheck_5333_ = (!crate::leanh::lean_is_exclusive(v___x_5321_)) as u8;
                    if v_isSharedCheck_5333_ == 0 {
                        v___x_5324_ = v___x_5321_;
                        v_isShared_5325_ = v_isSharedCheck_5333_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5322_);
                        crate::leanh::lean_dec(v___x_5321_);
                        v___x_5324_ = crate::leanh::lean_box(0);
                        v_isShared_5325_ = v_isSharedCheck_5333_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_5317_);
                    v_a_5334_ = crate::leanh::lean_ctor_get(v___x_5321_, 0);
                    v_isSharedCheck_5341_ = (!crate::leanh::lean_is_exclusive(v___x_5321_)) as u8;
                    if v_isSharedCheck_5341_ == 0 {
                        v___x_5336_ = v___x_5321_;
                        v_isShared_5337_ = v_isSharedCheck_5341_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5334_);
                        crate::leanh::lean_dec(v___x_5321_);
                        v___x_5336_ = crate::leanh::lean_box(0);
                        v_isShared_5337_ = v_isSharedCheck_5341_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_5326_ = crate::leanh::lean_ctor_get(v_a_5322_, 1);
                crate::leanh::lean_inc(v_levelParams_5326_);
                crate::leanh::lean_dec(v_a_5322_);
                v___x_5327_ = crate::leanh::lean_box(0);
                v___x_5328_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(v_levelParams_5326_, v___x_5327_);
                v___x_5329_ = l_Lean_mkConst(v_constName_5317_, v___x_5328_);
                if v_isShared_5325_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5324_, 0, v___x_5329_);
                    v___x_5331_ = v___x_5324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5332_, 0, v___x_5329_);
                    v___x_5331_ = v_reuseFailAlloc_5332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5331_;
            }
            3 => {
                if v_isShared_5337_ == 0 {
                    v___x_5339_ = v___x_5336_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
                    v___x_5339_ = v_reuseFailAlloc_5340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(
    mut v_constName_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5346_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(
        v_constName_5342_,
        v___y_5343_,
        v___y_5344_,
    );
    crate::leanh::lean_dec(v___y_5344_);
    crate::leanh::lean_dec_ref(v___y_5343_);
    return v_res_5346_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_printWarning___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5348_ = l_Lean_Linter_EnvLinter_printWarning___closed__0;
    v___x_5349_ = l_Lean_stringToMessageData(v___x_5348_);
    return v___x_5349_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_printWarning___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5351_ = l_Lean_Linter_EnvLinter_printWarning___closed__2;
    v___x_5352_ = l_Lean_stringToMessageData(v___x_5351_);
    return v___x_5352_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_printWarning___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5354_ = l_Lean_Linter_EnvLinter_printWarning___closed__4;
    v___x_5355_ = l_Lean_stringToMessageData(v___x_5354_);
    return v___x_5355_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_printWarning___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5357_ = l_Lean_Linter_EnvLinter_printWarning___closed__6;
    v___x_5358_ = l_Lean_stringToMessageData(v___x_5357_);
    return v___x_5358_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_printWarning___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5360_ = l_Lean_Linter_EnvLinter_printWarning___closed__8;
    v___x_5361_ = l_Lean_stringToMessageData(v___x_5360_);
    return v___x_5361_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_printWarning___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5363_ = l_Lean_Linter_EnvLinter_printWarning___closed__10;
    v___x_5364_ = l_Lean_stringToMessageData(v___x_5363_);
    return v___x_5364_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_printWarning(
    mut v_declName_5365_: *mut crate::leanh::LeanObject,
    mut v_warning_5366_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_5367_: u8,
    mut v_filePath_5368_: *mut crate::leanh::LeanObject,
    mut v_a_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5389_: u8 = 0;
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v_pos_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5441_: u8 = 0;
    let mut v_isSharedCheck_5442_: u8 = 0;
    let mut v_unused_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5447_: u8 = 0;
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5451_: u8 = 0;
    let mut v_isSharedCheck_5452_: u8 = 0;
    let mut v_a_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5456_: u8 = 0;
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useErrorFormat_5367_ == 0 {
                    crate::leanh::lean_dec_ref(v_filePath_5368_);
                    v___y_5373_ = v_a_5369_;
                    v___y_5374_ = v_a_5370_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_declName_5365_);
                    v___x_5394_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_5365_, v_a_5369_, v_a_5370_);
                    if crate::leanh::lean_obj_tag(v___x_5394_) == 0 {
                        v_a_5395_ = crate::leanh::lean_ctor_get(v___x_5394_, 0);
                        crate::leanh::lean_inc(v_a_5395_);
                        crate::leanh::lean_dec_ref_known(v___x_5394_, 1);
                        if crate::leanh::lean_obj_tag(v_a_5395_) == 1 {
                            v_val_5396_ = crate::leanh::lean_ctor_get(v_a_5395_, 0);
                            v_isSharedCheck_5452_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5395_)) as u8;
                            if v_isSharedCheck_5452_ == 0 {
                                v___x_5398_ = v_a_5395_;
                                v_isShared_5399_ = v_isSharedCheck_5452_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5396_);
                                crate::leanh::lean_dec(v_a_5395_);
                                v___x_5398_ = crate::leanh::lean_box(0);
                                v_isShared_5399_ = v_isSharedCheck_5452_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5395_);
                            crate::leanh::lean_dec_ref(v_filePath_5368_);
                            v___y_5373_ = v_a_5369_;
                            v___y_5374_ = v_a_5370_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_filePath_5368_);
                        crate::leanh::lean_dec_ref(v_warning_5366_);
                        crate::leanh::lean_dec(v_declName_5365_);
                        v_a_5453_ = crate::leanh::lean_ctor_get(v___x_5394_, 0);
                        v_isSharedCheck_5460_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5394_)) as u8;
                        if v_isSharedCheck_5460_ == 0 {
                            v___x_5455_ = v___x_5394_;
                            v_isShared_5456_ = v_isSharedCheck_5460_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5453_);
                            crate::leanh::lean_dec(v___x_5394_);
                            v___x_5455_ = crate::leanh::lean_box(0);
                            v_isShared_5456_ = v_isSharedCheck_5460_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5375_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_5365_, v___y_5373_, v___y_5374_);
                if crate::leanh::lean_obj_tag(v___x_5375_) == 0 {
                    v_a_5376_ = crate::leanh::lean_ctor_get(v___x_5375_, 0);
                    crate::leanh::lean_inc(v_a_5376_);
                    crate::leanh::lean_dec_ref_known(v___x_5375_, 1);
                    v___x_5377_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_printWarning___closed__1_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_printWarning___closed__1,
                    );
                    v___x_5378_ = l_Lean_MessageData_ofExpr(v_a_5376_);
                    v___x_5379_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5379_, 0, v___x_5377_);
                    crate::leanh::lean_ctor_set(v___x_5379_, 1, v___x_5378_);
                    v___x_5380_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_printWarning___closed__3_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_printWarning___closed__3,
                    );
                    v___x_5381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5381_, 0, v___x_5379_);
                    crate::leanh::lean_ctor_set(v___x_5381_, 1, v___x_5380_);
                    v___x_5382_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5382_, 0, v___x_5381_);
                    crate::leanh::lean_ctor_set(v___x_5382_, 1, v_warning_5366_);
                    v___x_5383_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_printWarning___closed__5_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_printWarning___closed__5,
                    );
                    v___x_5384_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5384_, 0, v___x_5382_);
                    crate::leanh::lean_ctor_set(v___x_5384_, 1, v___x_5383_);
                    v___x_5385_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_5384_, v___y_5373_, v___y_5374_);
                    return v___x_5385_;
                } else {
                    crate::leanh::lean_dec_ref(v_warning_5366_);
                    v_a_5386_ = crate::leanh::lean_ctor_get(v___x_5375_, 0);
                    v_isSharedCheck_5393_ = (!crate::leanh::lean_is_exclusive(v___x_5375_)) as u8;
                    if v_isSharedCheck_5393_ == 0 {
                        v___x_5388_ = v___x_5375_;
                        v_isShared_5389_ = v_isSharedCheck_5393_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5386_);
                        crate::leanh::lean_dec(v___x_5375_);
                        v___x_5388_ = crate::leanh::lean_box(0);
                        v_isShared_5389_ = v_isSharedCheck_5393_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5389_ == 0 {
                    v___x_5391_ = v___x_5388_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5392_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_a_5386_);
                    v___x_5391_ = v_reuseFailAlloc_5392_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5391_;
            }
            4 => {
                v___x_5400_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_5365_, v_a_5369_, v_a_5370_);
                if crate::leanh::lean_obj_tag(v___x_5400_) == 0 {
                    v_range_5401_ = crate::leanh::lean_ctor_get(v_val_5396_, 0);
                    v_isSharedCheck_5442_ = (!crate::leanh::lean_is_exclusive(v_val_5396_)) as u8;
                    if v_isSharedCheck_5442_ == 0 {
                        v_unused_5443_ = crate::leanh::lean_ctor_get(v_val_5396_, 1);
                        crate::leanh::lean_dec(v_unused_5443_);
                        v___x_5403_ = v_val_5396_;
                        v_isShared_5404_ = v_isSharedCheck_5442_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_range_5401_);
                        crate::leanh::lean_dec(v_val_5396_);
                        v___x_5403_ = crate::leanh::lean_box(0);
                        v_isShared_5404_ = v_isSharedCheck_5442_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5398_);
                    crate::leanh::lean_dec(v_val_5396_);
                    crate::leanh::lean_dec_ref(v_filePath_5368_);
                    crate::leanh::lean_dec_ref(v_warning_5366_);
                    v_a_5444_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                    v_isSharedCheck_5451_ = (!crate::leanh::lean_is_exclusive(v___x_5400_)) as u8;
                    if v_isSharedCheck_5451_ == 0 {
                        v___x_5446_ = v___x_5400_;
                        v_isShared_5447_ = v_isSharedCheck_5451_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5444_);
                        crate::leanh::lean_dec(v___x_5400_);
                        v___x_5446_ = crate::leanh::lean_box(0);
                        v_isShared_5447_ = v_isSharedCheck_5451_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v_pos_5405_ = crate::leanh::lean_ctor_get(v_range_5401_, 0);
                crate::leanh::lean_inc_ref(v_pos_5405_);
                crate::leanh::lean_dec_ref(v_range_5401_);
                v_a_5406_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                crate::leanh::lean_inc(v_a_5406_);
                crate::leanh::lean_dec_ref_known(v___x_5400_, 1);
                v_line_5407_ = crate::leanh::lean_ctor_get(v_pos_5405_, 0);
                v_column_5408_ = crate::leanh::lean_ctor_get(v_pos_5405_, 1);
                v_isSharedCheck_5441_ = (!crate::leanh::lean_is_exclusive(v_pos_5405_)) as u8;
                if v_isSharedCheck_5441_ == 0 {
                    v___x_5410_ = v_pos_5405_;
                    v_isShared_5411_ = v_isSharedCheck_5441_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_5408_);
                    crate::leanh::lean_inc(v_line_5407_);
                    crate::leanh::lean_dec(v_pos_5405_);
                    v___x_5410_ = crate::leanh::lean_box(0);
                    v_isShared_5411_ = v_isSharedCheck_5441_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5399_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5398_, 3);
                    crate::leanh::lean_ctor_set(v___x_5398_, 0, v_filePath_5368_);
                    v___x_5413_ = v___x_5398_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5440_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_filePath_5368_);
                    v___x_5413_ = v_reuseFailAlloc_5440_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5414_ = l_Lean_MessageData_ofFormat(v___x_5413_);
                v___x_5415_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__7_once),
                    _init_l_Lean_Linter_EnvLinter_printWarning___closed__7,
                );
                if v_isShared_5411_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5410_, 7);
                    crate::leanh::lean_ctor_set(v___x_5410_, 1, v___x_5415_);
                    crate::leanh::lean_ctor_set(v___x_5410_, 0, v___x_5414_);
                    v___x_5417_ = v___x_5410_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5439_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 0, v___x_5414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 1, v___x_5415_);
                    v___x_5417_ = v_reuseFailAlloc_5439_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5418_ = l_Nat_reprFast(v_line_5407_);
                v___x_5419_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5419_, 0, v___x_5418_);
                v___x_5420_ = l_Lean_MessageData_ofFormat(v___x_5419_);
                if v_isShared_5404_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5403_, 7);
                    crate::leanh::lean_ctor_set(v___x_5403_, 1, v___x_5420_);
                    crate::leanh::lean_ctor_set(v___x_5403_, 0, v___x_5417_);
                    v___x_5422_ = v___x_5403_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5438_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5438_, 1, v___x_5420_);
                    v___x_5422_ = v_reuseFailAlloc_5438_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5423_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5423_, 0, v___x_5422_);
                crate::leanh::lean_ctor_set(v___x_5423_, 1, v___x_5415_);
                v___x_5424_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5425_ = lean_nat_add(v_column_5408_, v___x_5424_);
                crate::leanh::lean_dec(v_column_5408_);
                v___x_5426_ = l_Nat_reprFast(v___x_5425_);
                v___x_5427_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5427_, 0, v___x_5426_);
                v___x_5428_ = l_Lean_MessageData_ofFormat(v___x_5427_);
                v___x_5429_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5429_, 0, v___x_5423_);
                crate::leanh::lean_ctor_set(v___x_5429_, 1, v___x_5428_);
                v___x_5430_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__9_once),
                    _init_l_Lean_Linter_EnvLinter_printWarning___closed__9,
                );
                v___x_5431_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5431_, 0, v___x_5429_);
                crate::leanh::lean_ctor_set(v___x_5431_, 1, v___x_5430_);
                v___x_5432_ = l_Lean_MessageData_ofExpr(v_a_5406_);
                v___x_5433_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5433_, 0, v___x_5431_);
                crate::leanh::lean_ctor_set(v___x_5433_, 1, v___x_5432_);
                v___x_5434_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__11_once),
                    _init_l_Lean_Linter_EnvLinter_printWarning___closed__11,
                );
                v___x_5435_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5435_, 0, v___x_5433_);
                crate::leanh::lean_ctor_set(v___x_5435_, 1, v___x_5434_);
                v___x_5436_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5436_, 0, v___x_5435_);
                crate::leanh::lean_ctor_set(v___x_5436_, 1, v_warning_5366_);
                v___x_5437_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_5436_, v_a_5369_, v_a_5370_);
                return v___x_5437_;
            }
            10 => {
                if v_isShared_5447_ == 0 {
                    v___x_5449_ = v___x_5446_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_a_5444_);
                    v___x_5449_ = v_reuseFailAlloc_5450_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5449_;
            }
            12 => {
                if v_isShared_5456_ == 0 {
                    v___x_5458_ = v___x_5455_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5453_);
                    v___x_5458_ = v_reuseFailAlloc_5459_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_printWarning___boxed(
    mut v_declName_5461_: *mut crate::leanh::LeanObject,
    mut v_warning_5462_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_5463_: *mut crate::leanh::LeanObject,
    mut v_filePath_5464_: *mut crate::leanh::LeanObject,
    mut v_a_5465_: *mut crate::leanh::LeanObject,
    mut v_a_5466_: *mut crate::leanh::LeanObject,
    mut v_a_5467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_5468_: u8 = 0;
    let mut v_res_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_5468_ = (crate::leanh::lean_unbox(v_useErrorFormat_5463_) as u8);
    v_res_5469_ = l_Lean_Linter_EnvLinter_printWarning(
        v_declName_5461_,
        v_warning_5462_,
        v_useErrorFormat_boxed_5468_,
        v_filePath_5464_,
        v_a_5465_,
        v_a_5466_,
    );
    crate::leanh::lean_dec(v_a_5466_);
    crate::leanh::lean_dec_ref(v_a_5465_);
    return v_res_5469_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(
    mut v_00_u03b1_5470_: *mut crate::leanh::LeanObject,
    mut v_constName_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
    mut v___y_5473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5475_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_5471_, v___y_5472_, v___y_5473_);
    return v___x_5475_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_5476_: *mut crate::leanh::LeanObject,
    mut v_constName_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5481_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(v_00_u03b1_5476_, v_constName_5477_, v___y_5478_, v___y_5479_);
    crate::leanh::lean_dec(v___y_5479_);
    crate::leanh::lean_dec_ref(v___y_5478_);
    return v_res_5481_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b1_5482_: *mut crate::leanh::LeanObject,
    mut v_ref_5483_: *mut crate::leanh::LeanObject,
    mut v_constName_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5488_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_5483_, v_constName_5484_, v___y_5485_, v___y_5486_);
    return v___x_5488_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_00_u03b1_5489_: *mut crate::leanh::LeanObject,
    mut v_ref_5490_: *mut crate::leanh::LeanObject,
    mut v_constName_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
    mut v___y_5494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5495_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_5489_, v_ref_5490_, v_constName_5491_, v___y_5492_, v___y_5493_);
    crate::leanh::lean_dec(v___y_5493_);
    crate::leanh::lean_dec_ref(v___y_5492_);
    crate::leanh::lean_dec(v_ref_5490_);
    return v_res_5495_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b1_5496_: *mut crate::leanh::LeanObject,
    mut v_ref_5497_: *mut crate::leanh::LeanObject,
    mut v_msg_5498_: *mut crate::leanh::LeanObject,
    mut v_declHint_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5503_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_5497_, v_msg_5498_, v_declHint_5499_, v___y_5500_, v___y_5501_);
    return v___x_5503_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_5504_: *mut crate::leanh::LeanObject,
    mut v_ref_5505_: *mut crate::leanh::LeanObject,
    mut v_msg_5506_: *mut crate::leanh::LeanObject,
    mut v_declHint_5507_: *mut crate::leanh::LeanObject,
    mut v___y_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
    mut v___y_5510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5511_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_5504_, v_ref_5505_, v_msg_5506_, v_declHint_5507_, v___y_5508_, v___y_5509_);
    crate::leanh::lean_dec(v___y_5509_);
    crate::leanh::lean_dec_ref(v___y_5508_);
    crate::leanh::lean_dec(v_ref_5505_);
    return v_res_5511_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(
    mut v_msg_5512_: *mut crate::leanh::LeanObject,
    mut v_declHint_5513_: *mut crate::leanh::LeanObject,
    mut v___y_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5517_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_5512_, v_declHint_5513_, v___y_5515_);
    return v___x_5517_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(
    mut v_msg_5518_: *mut crate::leanh::LeanObject,
    mut v_declHint_5519_: *mut crate::leanh::LeanObject,
    mut v___y_5520_: *mut crate::leanh::LeanObject,
    mut v___y_5521_: *mut crate::leanh::LeanObject,
    mut v___y_5522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5523_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_5518_, v_declHint_5519_, v___y_5520_, v___y_5521_);
    crate::leanh::lean_dec(v___y_5521_);
    crate::leanh::lean_dec_ref(v___y_5520_);
    return v_res_5523_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_5524_: *mut crate::leanh::LeanObject,
    mut v_ref_5525_: *mut crate::leanh::LeanObject,
    mut v_msg_5526_: *mut crate::leanh::LeanObject,
    mut v___y_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5530_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_5525_, v_msg_5526_, v___y_5527_, v___y_5528_);
    return v___x_5530_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_5531_: *mut crate::leanh::LeanObject,
    mut v_ref_5532_: *mut crate::leanh::LeanObject,
    mut v_msg_5533_: *mut crate::leanh::LeanObject,
    mut v___y_5534_: *mut crate::leanh::LeanObject,
    mut v___y_5535_: *mut crate::leanh::LeanObject,
    mut v___y_5536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5537_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_5531_, v_ref_5532_, v_msg_5533_, v___y_5534_, v___y_5535_);
    crate::leanh::lean_dec(v___y_5535_);
    crate::leanh::lean_dec_ref(v___y_5534_);
    crate::leanh::lean_dec(v_ref_5532_);
    return v_res_5537_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(
    mut v_00_u03b1_5538_: *mut crate::leanh::LeanObject,
    mut v_msg_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5543_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_5539_, v___y_5540_, v___y_5541_);
    return v___x_5543_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_5544_: *mut crate::leanh::LeanObject,
    mut v_msg_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5549_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_5544_, v_msg_5545_, v___y_5546_, v___y_5547_);
    crate::leanh::lean_dec(v___y_5547_);
    crate::leanh::lean_dec_ref(v___y_5546_);
    return v_res_5549_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(
    mut v_useErrorFormat_5550_: u8,
    mut v_filePath_5551_: *mut crate::leanh::LeanObject,
    mut v_sz_5552_: usize,
    mut v_i_5553_: usize,
    mut v_bs_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: usize = 0;
    let mut v___x_5568_: usize = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5558_ = lean_usize_dec_lt(v_i_5553_, v_sz_5552_);
                if v___x_5558_ == 0 {
                    crate::leanh::lean_dec_ref(v_filePath_5551_);
                    v___x_5559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5559_, 0, v_bs_5554_);
                    return v___x_5559_;
                } else {
                    v_v_5560_ = lean_array_uget_borrowed(v_bs_5554_, v_i_5553_);
                    v_fst_5561_ = crate::leanh::lean_ctor_get(v_v_5560_, 0);
                    v_snd_5562_ = crate::leanh::lean_ctor_get(v_v_5560_, 1);
                    crate::leanh::lean_inc_ref(v_filePath_5551_);
                    crate::leanh::lean_inc(v_snd_5562_);
                    crate::leanh::lean_inc(v_fst_5561_);
                    v___x_5563_ = l_Lean_Linter_EnvLinter_printWarning(
                        v_fst_5561_,
                        v_snd_5562_,
                        v_useErrorFormat_5550_,
                        v_filePath_5551_,
                        v___y_5555_,
                        v___y_5556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5563_) == 0 {
                        v_a_5564_ = crate::leanh::lean_ctor_get(v___x_5563_, 0);
                        crate::leanh::lean_inc(v_a_5564_);
                        crate::leanh::lean_dec_ref_known(v___x_5563_, 1);
                        v___x_5565_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5566_ = lean_array_uset(v_bs_5554_, v_i_5553_, v___x_5565_);
                        v___x_5567_ = 1usize;
                        v___x_5568_ = lean_usize_add(v_i_5553_, v___x_5567_);
                        v___x_5569_ = lean_array_uset(v_bs_x27_5566_, v_i_5553_, v_a_5564_);
                        v_i_5553_ = v___x_5568_;
                        v_bs_5554_ = v___x_5569_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5554_);
                        crate::leanh::lean_dec_ref(v_filePath_5551_);
                        v_a_5571_ = crate::leanh::lean_ctor_get(v___x_5563_, 0);
                        v_isSharedCheck_5578_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5563_)) as u8;
                        if v_isSharedCheck_5578_ == 0 {
                            v___x_5573_ = v___x_5563_;
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5571_);
                            crate::leanh::lean_dec(v___x_5563_);
                            v___x_5573_ = crate::leanh::lean_box(0);
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5574_ == 0 {
                    v___x_5576_ = v___x_5573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
                    v___x_5576_ = v_reuseFailAlloc_5577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(
    mut v_useErrorFormat_5579_: *mut crate::leanh::LeanObject,
    mut v_filePath_5580_: *mut crate::leanh::LeanObject,
    mut v_sz_5581_: *mut crate::leanh::LeanObject,
    mut v_i_5582_: *mut crate::leanh::LeanObject,
    mut v_bs_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_5587_: u8 = 0;
    let mut v_sz_boxed_5588_: usize = 0;
    let mut v_i_boxed_5589_: usize = 0;
    let mut v_res_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_5587_ = (crate::leanh::lean_unbox(v_useErrorFormat_5579_) as u8);
    v_sz_boxed_5588_ = crate::leanh::lean_unbox_usize(v_sz_5581_);
    crate::leanh::lean_dec(v_sz_5581_);
    v_i_boxed_5589_ = crate::leanh::lean_unbox_usize(v_i_5582_);
    crate::leanh::lean_dec(v_i_5582_);
    v_res_5590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_boxed_5587_, v_filePath_5580_, v_sz_boxed_5588_, v_i_boxed_5589_, v_bs_5583_, v___y_5584_, v___y_5585_);
    crate::leanh::lean_dec(v___y_5585_);
    crate::leanh::lean_dec_ref(v___y_5584_);
    return v_res_5590_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5591_ = crate::leanh::lean_box(1);
    v___x_5592_ = l_Lean_MessageData_ofFormat(v___x_5591_);
    return v___x_5592_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_printWarnings(
    mut v_results_5593_: *mut crate::leanh::LeanObject,
    mut v_filePath_5594_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_5595_: u8,
    mut v_a_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5601_: usize = 0;
    let mut v___x_5602_: usize = 0;
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5607_: u8 = 0;
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5614_: u8 = 0;
    let mut v_a_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5618_: u8 = 0;
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5622_: u8 = 0;
    let mut v_a_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5626_: u8 = 0;
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5599_ = l_Lean_Linter_EnvLinter_sortResults___redArg(
                    v_results_5593_,
                    v_a_5596_,
                    v_a_5597_,
                );
                if crate::leanh::lean_obj_tag(v___x_5599_) == 0 {
                    v_a_5600_ = crate::leanh::lean_ctor_get(v___x_5599_, 0);
                    crate::leanh::lean_inc(v_a_5600_);
                    crate::leanh::lean_dec_ref_known(v___x_5599_, 1);
                    v_sz_5601_ = lean_array_size(v_a_5600_);
                    v___x_5602_ = 0usize;
                    v___x_5603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_5595_, v_filePath_5594_, v_sz_5601_, v___x_5602_, v_a_5600_, v_a_5596_, v_a_5597_);
                    if crate::leanh::lean_obj_tag(v___x_5603_) == 0 {
                        v_a_5604_ = crate::leanh::lean_ctor_get(v___x_5603_, 0);
                        v_isSharedCheck_5614_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5603_)) as u8;
                        if v_isSharedCheck_5614_ == 0 {
                            v___x_5606_ = v___x_5603_;
                            v_isShared_5607_ = v_isSharedCheck_5614_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5604_);
                            crate::leanh::lean_dec(v___x_5603_);
                            v___x_5606_ = crate::leanh::lean_box(0);
                            v_isShared_5607_ = v_isSharedCheck_5614_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5615_ = crate::leanh::lean_ctor_get(v___x_5603_, 0);
                        v_isSharedCheck_5622_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5603_)) as u8;
                        if v_isSharedCheck_5622_ == 0 {
                            v___x_5617_ = v___x_5603_;
                            v_isShared_5618_ = v_isSharedCheck_5622_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5615_);
                            crate::leanh::lean_dec(v___x_5603_);
                            v___x_5617_ = crate::leanh::lean_box(0);
                            v_isShared_5618_ = v_isSharedCheck_5622_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_filePath_5594_);
                    v_a_5623_ = crate::leanh::lean_ctor_get(v___x_5599_, 0);
                    v_isSharedCheck_5630_ = (!crate::leanh::lean_is_exclusive(v___x_5599_)) as u8;
                    if v_isSharedCheck_5630_ == 0 {
                        v___x_5625_ = v___x_5599_;
                        v_isShared_5626_ = v_isSharedCheck_5630_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5623_);
                        crate::leanh::lean_dec(v___x_5599_);
                        v___x_5625_ = crate::leanh::lean_box(0);
                        v_isShared_5626_ = v_isSharedCheck_5630_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5608_ = lean_array_to_list(v_a_5604_);
                v___x_5609_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarnings___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarnings___closed__0_once),
                    _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0,
                );
                v___x_5610_ = l_Lean_MessageData_joinSep(v___x_5608_, v___x_5609_);
                if v_isShared_5607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5606_, 0, v___x_5610_);
                    v___x_5612_ = v___x_5606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5610_);
                    v___x_5612_ = v_reuseFailAlloc_5613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5612_;
            }
            3 => {
                if v_isShared_5618_ == 0 {
                    v___x_5620_ = v___x_5617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
                    v___x_5620_ = v_reuseFailAlloc_5621_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5620_;
            }
            5 => {
                if v_isShared_5626_ == 0 {
                    v___x_5628_ = v___x_5625_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
                    v___x_5628_ = v_reuseFailAlloc_5629_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5628_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_printWarnings___boxed(
    mut v_results_5631_: *mut crate::leanh::LeanObject,
    mut v_filePath_5632_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_5633_: *mut crate::leanh::LeanObject,
    mut v_a_5634_: *mut crate::leanh::LeanObject,
    mut v_a_5635_: *mut crate::leanh::LeanObject,
    mut v_a_5636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_5637_: u8 = 0;
    let mut v_res_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_5637_ = (crate::leanh::lean_unbox(v_useErrorFormat_5633_) as u8);
    v_res_5638_ = l_Lean_Linter_EnvLinter_printWarnings(
        v_results_5631_,
        v_filePath_5632_,
        v_useErrorFormat_boxed_5637_,
        v_a_5634_,
        v_a_5635_,
    );
    crate::leanh::lean_dec(v_a_5635_);
    crate::leanh::lean_dec_ref(v_a_5634_);
    crate::leanh::lean_dec_ref(v_results_5631_);
    return v_res_5638_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(
    mut v_x_5639_: *mut crate::leanh::LeanObject,
    mut v_x_5640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5640_) == 0 {
                    return v_x_5639_;
                } else {
                    v_key_5641_ = crate::leanh::lean_ctor_get(v_x_5640_, 0);
                    v_value_5642_ = crate::leanh::lean_ctor_get(v_x_5640_, 1);
                    v_tail_5643_ = crate::leanh::lean_ctor_get(v_x_5640_, 2);
                    crate::leanh::lean_inc(v_value_5642_);
                    crate::leanh::lean_inc(v_key_5641_);
                    v___x_5644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5644_, 0, v_key_5641_);
                    crate::leanh::lean_ctor_set(v___x_5644_, 1, v_value_5642_);
                    v___x_5645_ = lean_array_push(v_x_5639_, v___x_5644_);
                    v_x_5639_ = v___x_5645_;
                    v_x_5640_ = v_tail_5643_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(
    mut v_x_5647_: *mut crate::leanh::LeanObject,
    mut v_x_5648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5649_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_x_5647_, v_x_5648_);
    crate::leanh::lean_dec(v_x_5648_);
    return v_res_5649_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(
    mut v_as_5650_: *mut crate::leanh::LeanObject,
    mut v_i_5651_: usize,
    mut v_stop_5652_: usize,
    mut v_b_5653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5654_: u8 = 0;
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: usize = 0;
    let mut v___x_5658_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5654_ = lean_usize_dec_eq(v_i_5651_, v_stop_5652_);
                if v___x_5654_ == 0 {
                    v___x_5655_ = lean_array_uget_borrowed(v_as_5650_, v_i_5651_);
                    v___x_5656_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_b_5653_, v___x_5655_);
                    v___x_5657_ = 1usize;
                    v___x_5658_ = lean_usize_add(v_i_5651_, v___x_5657_);
                    v_i_5651_ = v___x_5658_;
                    v_b_5653_ = v___x_5656_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5653_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(
    mut v_as_5660_: *mut crate::leanh::LeanObject,
    mut v_i_5661_: *mut crate::leanh::LeanObject,
    mut v_stop_5662_: *mut crate::leanh::LeanObject,
    mut v_b_5663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5664_: usize = 0;
    let mut v_stop_boxed_5665_: usize = 0;
    let mut v_res_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5664_ = crate::leanh::lean_unbox_usize(v_i_5661_);
    crate::leanh::lean_dec(v_i_5661_);
    v_stop_boxed_5665_ = crate::leanh::lean_unbox_usize(v_stop_5662_);
    crate::leanh::lean_dec(v_stop_5662_);
    v_res_5666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_as_5660_, v_i_boxed_5664_, v_stop_boxed_5665_, v_b_5663_);
    crate::leanh::lean_dec_ref(v_as_5660_);
    return v_res_5666_;
}
pub unsafe fn _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5668_ =
        l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0;
    v___x_5669_ = l_Lean_stringToMessageData(v___x_5668_);
    return v___x_5669_;
}
pub unsafe fn _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5671_ =
        l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2;
    v___x_5672_ = l_Lean_stringToMessageData(v___x_5671_);
    return v___x_5672_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(
    mut v_useErrorFormat_5673_: u8,
    mut v_x_5674_: *mut crate::leanh::LeanObject,
    mut v_x_5675_: *mut crate::leanh::LeanObject,
    mut v___y_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5685_: u8 = 0;
    let mut v_a_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5696_: u8 = 0;
    let mut v_fst_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5701_: u8 = 0;
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5718_: u8 = 0;
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5722_: u8 = 0;
    let mut v_isSharedCheck_5723_: u8 = 0;
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut v_isSharedCheck_5725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5674_) == 0 {
                    v___x_5679_ = l_List_reverse___redArg(v_x_5675_);
                    v___x_5680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5680_, 0, v___x_5679_);
                    return v___x_5680_;
                } else {
                    v_head_5681_ = crate::leanh::lean_ctor_get(v_x_5674_, 0);
                    v_tail_5682_ = crate::leanh::lean_ctor_get(v_x_5674_, 1);
                    v_isSharedCheck_5725_ = (!crate::leanh::lean_is_exclusive(v_x_5674_)) as u8;
                    if v_isSharedCheck_5725_ == 0 {
                        v___x_5684_ = v_x_5674_;
                        v_isShared_5685_ = v_isSharedCheck_5725_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5682_);
                        crate::leanh::lean_inc(v_head_5681_);
                        crate::leanh::lean_dec(v_x_5674_);
                        v___x_5684_ = crate::leanh::lean_box(0);
                        v_isShared_5685_ = v_isSharedCheck_5725_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5692_ = crate::leanh::lean_ctor_get(v_head_5681_, 1);
                v_fst_5693_ = crate::leanh::lean_ctor_get(v_head_5681_, 0);
                v_isSharedCheck_5724_ = (!crate::leanh::lean_is_exclusive(v_head_5681_)) as u8;
                if v_isSharedCheck_5724_ == 0 {
                    v___x_5695_ = v_head_5681_;
                    v_isShared_5696_ = v_isSharedCheck_5724_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5692_);
                    crate::leanh::lean_inc(v_fst_5693_);
                    crate::leanh::lean_dec(v_head_5681_);
                    v___x_5695_ = crate::leanh::lean_box(0);
                    v_isShared_5696_ = v_isSharedCheck_5724_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_5685_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5684_, 1, v_x_5675_);
                    crate::leanh::lean_ctor_set(v___x_5684_, 0, v_a_5687_);
                    v___x_5689_ = v___x_5684_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5691_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_a_5687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5691_, 1, v_x_5675_);
                    v___x_5689_ = v_reuseFailAlloc_5691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_5674_ = v_tail_5682_;
                v_x_5675_ = v___x_5689_;
                state = 0;
                continue;
            }
            4 => {
                v_fst_5697_ = crate::leanh::lean_ctor_get(v_snd_5692_, 0);
                v_snd_5698_ = crate::leanh::lean_ctor_get(v_snd_5692_, 1);
                v_isSharedCheck_5723_ = (!crate::leanh::lean_is_exclusive(v_snd_5692_)) as u8;
                if v_isSharedCheck_5723_ == 0 {
                    v___x_5700_ = v_snd_5692_;
                    v_isShared_5701_ = v_isSharedCheck_5723_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5698_);
                    crate::leanh::lean_inc(v_fst_5697_);
                    crate::leanh::lean_dec(v_snd_5692_);
                    v___x_5700_ = crate::leanh::lean_box(0);
                    v_isShared_5701_ = v_isSharedCheck_5723_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5702_ = l_Lean_Linter_EnvLinter_printWarnings(
                    v_snd_5698_,
                    v_fst_5697_,
                    v_useErrorFormat_5673_,
                    v___y_5676_,
                    v___y_5677_,
                );
                crate::leanh::lean_dec(v_snd_5698_);
                if crate::leanh::lean_obj_tag(v___x_5702_) == 0 {
                    v_a_5703_ = crate::leanh::lean_ctor_get(v___x_5702_, 0);
                    crate::leanh::lean_inc(v_a_5703_);
                    crate::leanh::lean_dec_ref_known(v___x_5702_, 1);
                    v___x_5704_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1), core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once), _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1);
                    v___x_5705_ = l_Lean_MessageData_ofName(v_fst_5693_);
                    if v_isShared_5701_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5700_, 7);
                        crate::leanh::lean_ctor_set(v___x_5700_, 1, v___x_5705_);
                        crate::leanh::lean_ctor_set(v___x_5700_, 0, v___x_5704_);
                        v___x_5707_ = v___x_5700_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5704_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 1, v___x_5705_);
                        v___x_5707_ = v_reuseFailAlloc_5713_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5700_);
                    crate::leanh::lean_del_object(v___x_5695_);
                    crate::leanh::lean_dec(v_fst_5693_);
                    if crate::leanh::lean_obj_tag(v___x_5702_) == 0 {
                        v_a_5714_ = crate::leanh::lean_ctor_get(v___x_5702_, 0);
                        crate::leanh::lean_inc(v_a_5714_);
                        crate::leanh::lean_dec_ref_known(v___x_5702_, 1);
                        v_a_5687_ = v_a_5714_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5684_);
                        crate::leanh::lean_dec(v_tail_5682_);
                        crate::leanh::lean_dec(v_x_5675_);
                        v_a_5715_ = crate::leanh::lean_ctor_get(v___x_5702_, 0);
                        v_isSharedCheck_5722_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5702_)) as u8;
                        if v_isSharedCheck_5722_ == 0 {
                            v___x_5717_ = v___x_5702_;
                            v_isShared_5718_ = v_isSharedCheck_5722_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5715_);
                            crate::leanh::lean_dec(v___x_5702_);
                            v___x_5717_ = crate::leanh::lean_box(0);
                            v_isShared_5718_ = v_isSharedCheck_5722_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_5708_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3), core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once), _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
                if v_isShared_5696_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5695_, 7);
                    crate::leanh::lean_ctor_set(v___x_5695_, 1, v___x_5708_);
                    crate::leanh::lean_ctor_set(v___x_5695_, 0, v___x_5707_);
                    v___x_5710_ = v___x_5695_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5712_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5712_, 0, v___x_5707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5712_, 1, v___x_5708_);
                    v___x_5710_ = v_reuseFailAlloc_5712_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5711_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5711_, 0, v___x_5710_);
                crate::leanh::lean_ctor_set(v___x_5711_, 1, v_a_5703_);
                v_a_5687_ = v___x_5711_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5718_ == 0 {
                    v___x_5720_ = v___x_5717_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_a_5715_);
                    v___x_5720_ = v_reuseFailAlloc_5721_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(
    mut v_useErrorFormat_5726_: *mut crate::leanh::LeanObject,
    mut v_x_5727_: *mut crate::leanh::LeanObject,
    mut v_x_5728_: *mut crate::leanh::LeanObject,
    mut v___y_5729_: *mut crate::leanh::LeanObject,
    mut v___y_5730_: *mut crate::leanh::LeanObject,
    mut v___y_5731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_5732_: u8 = 0;
    let mut v_res_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_5732_ = (crate::leanh::lean_unbox(v_useErrorFormat_5726_) as u8);
    v_res_5733_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(
        v_useErrorFormat_boxed_5732_,
        v_x_5727_,
        v_x_5728_,
        v___y_5729_,
        v___y_5730_,
    );
    crate::leanh::lean_dec(v___y_5730_);
    crate::leanh::lean_dec_ref(v___y_5729_);
    return v_res_5733_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(
    mut v_a_5734_: *mut crate::leanh::LeanObject,
    mut v_x_5735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5735_) == 0 {
                    v___x_5736_ = crate::leanh::lean_box(0);
                    return v___x_5736_;
                } else {
                    v_key_5737_ = crate::leanh::lean_ctor_get(v_x_5735_, 0);
                    v_value_5738_ = crate::leanh::lean_ctor_get(v_x_5735_, 1);
                    v_tail_5739_ = crate::leanh::lean_ctor_get(v_x_5735_, 2);
                    v___x_5740_ = lean_name_eq(v_key_5737_, v_a_5734_);
                    if v___x_5740_ == 0 {
                        v_x_5735_ = v_tail_5739_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5738_);
                        v___x_5742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5742_, 0, v_value_5738_);
                        return v___x_5742_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(
    mut v_a_5743_: *mut crate::leanh::LeanObject,
    mut v_x_5744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5745_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_5743_, v_x_5744_);
    crate::leanh::lean_dec(v_x_5744_);
    crate::leanh::lean_dec(v_a_5743_);
    return v_res_5745_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(
    mut v_m_5746_: *mut crate::leanh::LeanObject,
    mut v_a_5747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5751_: u64 = 0;
    let mut v___x_5752_: u64 = 0;
    let mut v___x_5753_: u64 = 0;
    let mut v_fold_5754_: u64 = 0;
    let mut v___x_5755_: u64 = 0;
    let mut v___x_5756_: u64 = 0;
    let mut v___x_5757_: u64 = 0;
    let mut v___x_5758_: usize = 0;
    let mut v___x_5759_: usize = 0;
    let mut v___x_5760_: usize = 0;
    let mut v___x_5761_: usize = 0;
    let mut v___x_5762_: usize = 0;
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: u64 = 0;
    let mut v_hash_5766_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5748_ = crate::leanh::lean_ctor_get(v_m_5746_, 1);
                v___x_5749_ = lean_array_get_size(v_buckets_5748_);
                if crate::leanh::lean_obj_tag(v_a_5747_) == 0 {
                    v___x_5765_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
                    v___y_5751_ = v___x_5765_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5766_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_5747_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5751_ = v_hash_5766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5752_ = 32u64;
                v___x_5753_ = lean_uint64_shift_right(v___y_5751_, v___x_5752_);
                v_fold_5754_ = lean_uint64_xor(v___y_5751_, v___x_5753_);
                v___x_5755_ = 16u64;
                v___x_5756_ = lean_uint64_shift_right(v_fold_5754_, v___x_5755_);
                v___x_5757_ = lean_uint64_xor(v_fold_5754_, v___x_5756_);
                v___x_5758_ = lean_uint64_to_usize(v___x_5757_);
                v___x_5759_ = lean_usize_of_nat(v___x_5749_);
                v___x_5760_ = 1usize;
                v___x_5761_ = lean_usize_sub(v___x_5759_, v___x_5760_);
                v___x_5762_ = lean_usize_land(v___x_5758_, v___x_5761_);
                v___x_5763_ = lean_array_uget_borrowed(v_buckets_5748_, v___x_5762_);
                v___x_5764_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_5747_, v___x_5763_);
                return v___x_5764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(
    mut v_m_5767_: *mut crate::leanh::LeanObject,
    mut v_a_5768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5769_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_5767_, v_a_5768_);
    crate::leanh::lean_dec(v_a_5768_);
    crate::leanh::lean_dec_ref(v_m_5767_);
    return v_res_5769_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(
    mut v_key_5770_: *mut crate::leanh::LeanObject,
    mut v_value_5771_: *mut crate::leanh::LeanObject,
    mut v_fp_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5776_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
    v___x_5777_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v___x_5776_, v_key_5770_, v_value_5771_);
    v___x_5778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5778_, 0, v_fp_5772_);
    crate::leanh::lean_ctor_set(v___x_5778_, 1, v___x_5777_);
    v___x_5779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5779_, 0, v___x_5778_);
    return v___x_5779_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(
    mut v_key_5780_: *mut crate::leanh::LeanObject,
    mut v_value_5781_: *mut crate::leanh::LeanObject,
    mut v_fp_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5786_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_5780_, v_value_5781_, v_fp_5782_, v___y_5783_, v___y_5784_);
    crate::leanh::lean_dec(v___y_5784_);
    crate::leanh::lean_dec_ref(v___y_5783_);
    return v_res_5786_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(
    mut v_constName_5787_: *mut crate::leanh::LeanObject,
    mut v___y_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: u8 = 0;
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5799_: u8 = 0;
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5791_ = lean_st_ref_get(v___y_5789_);
                v_env_5792_ = crate::leanh::lean_ctor_get(v___x_5791_, 0);
                crate::leanh::lean_inc_ref(v_env_5792_);
                crate::leanh::lean_dec(v___x_5791_);
                v___x_5793_ = 0;
                crate::leanh::lean_inc(v_constName_5787_);
                v___x_5794_ =
                    l_Lean_Environment_find_x3f(v_env_5792_, v_constName_5787_, v___x_5793_);
                if crate::leanh::lean_obj_tag(v___x_5794_) == 0 {
                    v___x_5795_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_5787_, v___y_5788_, v___y_5789_);
                    return v___x_5795_;
                } else {
                    crate::leanh::lean_dec(v_constName_5787_);
                    v_val_5796_ = crate::leanh::lean_ctor_get(v___x_5794_, 0);
                    v_isSharedCheck_5803_ = (!crate::leanh::lean_is_exclusive(v___x_5794_)) as u8;
                    if v_isSharedCheck_5803_ == 0 {
                        v___x_5798_ = v___x_5794_;
                        v_isShared_5799_ = v_isSharedCheck_5803_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5796_);
                        crate::leanh::lean_dec(v___x_5794_);
                        v___x_5798_ = crate::leanh::lean_box(0);
                        v_isShared_5799_ = v_isSharedCheck_5803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5799_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5798_, 0);
                    v___x_5801_ = v___x_5798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_val_5796_);
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
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(
    mut v_constName_5804_: *mut crate::leanh::LeanObject,
    mut v___y_5805_: *mut crate::leanh::LeanObject,
    mut v___y_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5808_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_constName_5804_, v___y_5805_, v___y_5806_);
    crate::leanh::lean_dec(v___y_5806_);
    crate::leanh::lean_dec_ref(v___y_5805_);
    return v_res_5808_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(
    mut v_declName_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5816_: u8 = 0;
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5827_: u8 = 0;
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5839_: u8 = 0;
    let mut v_isSharedCheck_5840_: u8 = 0;
    let mut v_unused_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5845_: u8 = 0;
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_5809_);
                v___x_5813_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_declName_5809_, v___y_5810_, v___y_5811_);
                if crate::leanh::lean_obj_tag(v___x_5813_) == 0 {
                    v_isSharedCheck_5840_ = (!crate::leanh::lean_is_exclusive(v___x_5813_)) as u8;
                    if v_isSharedCheck_5840_ == 0 {
                        v_unused_5841_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                        crate::leanh::lean_dec(v_unused_5841_);
                        v___x_5815_ = v___x_5813_;
                        v_isShared_5816_ = v_isSharedCheck_5840_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5813_);
                        v___x_5815_ = crate::leanh::lean_box(0);
                        v_isShared_5816_ = v_isSharedCheck_5840_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_5809_);
                    v_a_5842_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                    v_isSharedCheck_5849_ = (!crate::leanh::lean_is_exclusive(v___x_5813_)) as u8;
                    if v_isSharedCheck_5849_ == 0 {
                        v___x_5844_ = v___x_5813_;
                        v_isShared_5845_ = v_isSharedCheck_5849_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5842_);
                        crate::leanh::lean_dec(v___x_5813_);
                        v___x_5844_ = crate::leanh::lean_box(0);
                        v_isShared_5845_ = v_isSharedCheck_5849_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5817_ = lean_st_ref_get(v___y_5811_);
                v_env_5818_ = crate::leanh::lean_ctor_get(v___x_5817_, 0);
                crate::leanh::lean_inc_ref(v_env_5818_);
                crate::leanh::lean_dec(v___x_5817_);
                v___x_5819_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5818_, v_declName_5809_);
                crate::leanh::lean_dec(v_declName_5809_);
                crate::leanh::lean_dec_ref(v_env_5818_);
                if crate::leanh::lean_obj_tag(v___x_5819_) == 0 {
                    v___x_5820_ = crate::leanh::lean_box(0);
                    if v_isShared_5816_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5815_, 0, v___x_5820_);
                        v___x_5822_ = v___x_5815_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 0, v___x_5820_);
                        v___x_5822_ = v_reuseFailAlloc_5823_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5824_ = crate::leanh::lean_ctor_get(v___x_5819_, 0);
                    v_isSharedCheck_5839_ = (!crate::leanh::lean_is_exclusive(v___x_5819_)) as u8;
                    if v_isSharedCheck_5839_ == 0 {
                        v___x_5826_ = v___x_5819_;
                        v_isShared_5827_ = v_isSharedCheck_5839_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5824_);
                        crate::leanh::lean_dec(v___x_5819_);
                        v___x_5826_ = crate::leanh::lean_box(0);
                        v_isShared_5827_ = v_isSharedCheck_5839_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5822_;
            }
            3 => {
                v___x_5828_ = lean_st_ref_get(v___y_5811_);
                v_env_5829_ = crate::leanh::lean_ctor_get(v___x_5828_, 0);
                crate::leanh::lean_inc_ref(v_env_5829_);
                crate::leanh::lean_dec(v___x_5828_);
                v___x_5830_ = crate::leanh::lean_box(0);
                v___x_5831_ = l_Lean_Environment_allImportedModuleNames(v_env_5829_);
                crate::leanh::lean_dec_ref(v_env_5829_);
                v___x_5832_ = lean_array_get(v___x_5830_, v___x_5831_, v_val_5824_);
                crate::leanh::lean_dec(v_val_5824_);
                crate::leanh::lean_dec_ref(v___x_5831_);
                if v_isShared_5827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5826_, 0, v___x_5832_);
                    v___x_5834_ = v___x_5826_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 0, v___x_5832_);
                    v___x_5834_ = v_reuseFailAlloc_5838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5815_, 0, v___x_5834_);
                    v___x_5836_ = v___x_5815_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5834_);
                    v___x_5836_ = v_reuseFailAlloc_5837_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5836_;
            }
            6 => {
                if v_isShared_5845_ == 0 {
                    v___x_5847_ = v___x_5844_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5848_, 0, v_a_5842_);
                    v___x_5847_ = v_reuseFailAlloc_5848_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(
    mut v_declName_5850_: *mut crate::leanh::LeanObject,
    mut v___y_5851_: *mut crate::leanh::LeanObject,
    mut v___y_5852_: *mut crate::leanh::LeanObject,
    mut v___y_5853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5854_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(
        v_declName_5850_,
        v___y_5851_,
        v___y_5852_,
    );
    crate::leanh::lean_dec(v___y_5852_);
    crate::leanh::lean_dec_ref(v___y_5851_);
    return v_res_5854_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(
    mut v_useErrorFormat_5858_: u8,
    mut v_sp_5859_: *mut crate::leanh::LeanObject,
    mut v_x_5860_: *mut crate::leanh::LeanObject,
    mut v_x_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5897_: u8 = 0;
    let mut v_ref_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut v_val_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5912_: u8 = 0;
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5917_: u8 = 0;
    let mut v_env_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5924_: u8 = 0;
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5861_) == 0 {
                    crate::leanh::lean_dec(v_sp_5859_);
                    v___x_5865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5865_, 0, v_x_5860_);
                    return v___x_5865_;
                } else {
                    v_key_5866_ = crate::leanh::lean_ctor_get(v_x_5861_, 0);
                    crate::leanh::lean_inc_n(v_key_5866_, 2);
                    v_value_5867_ = crate::leanh::lean_ctor_get(v_x_5861_, 1);
                    crate::leanh::lean_inc(v_value_5867_);
                    v_tail_5868_ = crate::leanh::lean_ctor_get(v_x_5861_, 2);
                    crate::leanh::lean_inc(v_tail_5868_);
                    crate::leanh::lean_dec_ref_known(v_x_5861_, 3);
                    v___x_5878_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_key_5866_, v___y_5862_, v___y_5863_);
                    if crate::leanh::lean_obj_tag(v___x_5878_) == 0 {
                        v_a_5879_ = crate::leanh::lean_ctor_get(v___x_5878_, 0);
                        crate::leanh::lean_inc(v_a_5879_);
                        crate::leanh::lean_dec_ref_known(v___x_5878_, 1);
                        v___x_5880_ = lean_st_ref_get(v___y_5863_);
                        if crate::leanh::lean_obj_tag(v_a_5879_) == 0 {
                            v_env_5918_ = crate::leanh::lean_ctor_get(v___x_5880_, 0);
                            crate::leanh::lean_inc_ref(v_env_5918_);
                            crate::leanh::lean_dec(v___x_5880_);
                            v___x_5919_ = l_Lean_Environment_mainModule(v_env_5918_);
                            crate::leanh::lean_dec_ref(v_env_5918_);
                            v___y_5882_ = v___x_5919_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5880_);
                            v_val_5920_ = crate::leanh::lean_ctor_get(v_a_5879_, 0);
                            crate::leanh::lean_inc(v_val_5920_);
                            crate::leanh::lean_dec_ref_known(v_a_5879_, 1);
                            v___y_5882_ = v_val_5920_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_5868_);
                        crate::leanh::lean_dec(v_value_5867_);
                        crate::leanh::lean_dec(v_key_5866_);
                        crate::leanh::lean_dec_ref(v_x_5860_);
                        crate::leanh::lean_dec(v_sp_5859_);
                        v_a_5921_ = crate::leanh::lean_ctor_get(v___x_5878_, 0);
                        v_isSharedCheck_5928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5878_)) as u8;
                        if v_isSharedCheck_5928_ == 0 {
                            v___x_5923_ = v___x_5878_;
                            v_isShared_5924_ = v_isSharedCheck_5928_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5921_);
                            crate::leanh::lean_dec(v___x_5878_);
                            v___x_5923_ = crate::leanh::lean_box(0);
                            v_isShared_5924_ = v_isSharedCheck_5928_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5872_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_x_5860_, v___y_5870_, v_a_5871_);
                v_x_5860_ = v___x_5872_;
                v_x_5861_ = v_tail_5868_;
                state = 0;
                continue;
            }
            2 => {
                v_a_5877_ = crate::leanh::lean_ctor_get(v___y_5876_, 0);
                crate::leanh::lean_inc(v_a_5877_);
                crate::leanh::lean_dec_ref(v___y_5876_);
                v___y_5870_ = v___y_5875_;
                v_a_5871_ = v_a_5877_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_x_5860_, v___y_5882_);
                if crate::leanh::lean_obj_tag(v___x_5883_) == 0 {
                    if v_useErrorFormat_5858_ == 0 {
                        v___x_5884_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0;
                        v___x_5885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_5866_, v_value_5867_, v___x_5884_, v___y_5862_, v___y_5863_);
                        v___y_5875_ = v___y_5882_;
                        v___y_5876_ = v___x_5885_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5886_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1;
                        crate::leanh::lean_inc(v___y_5882_);
                        crate::leanh::lean_inc(v_sp_5859_);
                        v___x_5887_ =
                            l_Lean_SearchPath_findWithExt(v_sp_5859_, v___x_5886_, v___y_5882_);
                        if crate::leanh::lean_obj_tag(v___x_5887_) == 0 {
                            v_a_5888_ = crate::leanh::lean_ctor_get(v___x_5887_, 0);
                            crate::leanh::lean_inc(v_a_5888_);
                            crate::leanh::lean_dec_ref_known(v___x_5887_, 1);
                            if crate::leanh::lean_obj_tag(v_a_5888_) == 0 {
                                v___x_5889_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2;
                                crate::leanh::lean_inc(v___y_5882_);
                                v___x_5890_ =
                                    l_Lean_modToFilePath(v___x_5889_, v___y_5882_, v___x_5886_);
                                v___x_5891_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_5866_, v_value_5867_, v___x_5890_, v___y_5862_, v___y_5863_);
                                v___y_5875_ = v___y_5882_;
                                v___y_5876_ = v___x_5891_;
                                state = 2;
                                continue;
                            } else {
                                v_val_5892_ = crate::leanh::lean_ctor_get(v_a_5888_, 0);
                                crate::leanh::lean_inc(v_val_5892_);
                                crate::leanh::lean_dec_ref_known(v_a_5888_, 1);
                                v___x_5893_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_5866_, v_value_5867_, v_val_5892_, v___y_5862_, v___y_5863_);
                                v___y_5875_ = v___y_5882_;
                                v___y_5876_ = v___x_5893_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_5882_);
                            crate::leanh::lean_dec(v_tail_5868_);
                            crate::leanh::lean_dec(v_value_5867_);
                            crate::leanh::lean_dec(v_key_5866_);
                            crate::leanh::lean_dec_ref(v_x_5860_);
                            crate::leanh::lean_dec(v_sp_5859_);
                            v_a_5894_ = crate::leanh::lean_ctor_get(v___x_5887_, 0);
                            v_isSharedCheck_5906_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5887_)) as u8;
                            if v_isSharedCheck_5906_ == 0 {
                                v___x_5896_ = v___x_5887_;
                                v_isShared_5897_ = v_isSharedCheck_5906_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5894_);
                                crate::leanh::lean_dec(v___x_5887_);
                                v___x_5896_ = crate::leanh::lean_box(0);
                                v_isShared_5897_ = v_isSharedCheck_5906_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    v_val_5907_ = crate::leanh::lean_ctor_get(v___x_5883_, 0);
                    crate::leanh::lean_inc(v_val_5907_);
                    crate::leanh::lean_dec_ref_known(v___x_5883_, 1);
                    v_fst_5908_ = crate::leanh::lean_ctor_get(v_val_5907_, 0);
                    v_snd_5909_ = crate::leanh::lean_ctor_get(v_val_5907_, 1);
                    v_isSharedCheck_5917_ = (!crate::leanh::lean_is_exclusive(v_val_5907_)) as u8;
                    if v_isSharedCheck_5917_ == 0 {
                        v___x_5911_ = v_val_5907_;
                        v_isShared_5912_ = v_isSharedCheck_5917_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5909_);
                        crate::leanh::lean_inc(v_fst_5908_);
                        crate::leanh::lean_dec(v_val_5907_);
                        v___x_5911_ = crate::leanh::lean_box(0);
                        v_isShared_5912_ = v_isSharedCheck_5917_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v_ref_5898_ = crate::leanh::lean_ctor_get(v___y_5862_, 5);
                v___x_5899_ = lean_io_error_to_string(v_a_5894_);
                v___x_5900_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5900_, 0, v___x_5899_);
                v___x_5901_ = l_Lean_MessageData_ofFormat(v___x_5900_);
                crate::leanh::lean_inc(v_ref_5898_);
                v___x_5902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5902_, 0, v_ref_5898_);
                crate::leanh::lean_ctor_set(v___x_5902_, 1, v___x_5901_);
                if v_isShared_5897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5896_, 0, v___x_5902_);
                    v___x_5904_ = v___x_5896_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5905_, 0, v___x_5902_);
                    v___x_5904_ = v_reuseFailAlloc_5905_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5904_;
            }
            6 => {
                v___x_5913_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_snd_5909_, v_key_5866_, v_value_5867_);
                if v_isShared_5912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5911_, 1, v___x_5913_);
                    v___x_5915_ = v___x_5911_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v_fst_5908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 1, v___x_5913_);
                    v___x_5915_ = v_reuseFailAlloc_5916_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5870_ = v___y_5882_;
                v_a_5871_ = v___x_5915_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_5924_ == 0 {
                    v___x_5926_ = v___x_5923_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_a_5921_);
                    v___x_5926_ = v_reuseFailAlloc_5927_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(
    mut v_useErrorFormat_5929_: *mut crate::leanh::LeanObject,
    mut v_sp_5930_: *mut crate::leanh::LeanObject,
    mut v_x_5931_: *mut crate::leanh::LeanObject,
    mut v_x_5932_: *mut crate::leanh::LeanObject,
    mut v___y_5933_: *mut crate::leanh::LeanObject,
    mut v___y_5934_: *mut crate::leanh::LeanObject,
    mut v___y_5935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_5936_: u8 = 0;
    let mut v_res_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_5936_ = (crate::leanh::lean_unbox(v_useErrorFormat_5929_) as u8);
    v_res_5937_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_boxed_5936_, v_sp_5930_, v_x_5931_, v_x_5932_, v___y_5933_, v___y_5934_);
    crate::leanh::lean_dec(v___y_5934_);
    crate::leanh::lean_dec_ref(v___y_5933_);
    return v_res_5937_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(
    mut v_useErrorFormat_5938_: u8,
    mut v_sp_5939_: *mut crate::leanh::LeanObject,
    mut v_as_5940_: *mut crate::leanh::LeanObject,
    mut v_i_5941_: usize,
    mut v_stop_5942_: usize,
    mut v_b_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
    mut v___y_5945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5947_: u8 = 0;
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: usize = 0;
    let mut v___x_5952_: usize = 0;
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5947_ = lean_usize_dec_eq(v_i_5941_, v_stop_5942_);
                if v___x_5947_ == 0 {
                    v___x_5948_ = lean_array_uget_borrowed(v_as_5940_, v_i_5941_);
                    crate::leanh::lean_inc(v___x_5948_);
                    crate::leanh::lean_inc(v_sp_5939_);
                    v___x_5949_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_5938_, v_sp_5939_, v_b_5943_, v___x_5948_, v___y_5944_, v___y_5945_);
                    if crate::leanh::lean_obj_tag(v___x_5949_) == 0 {
                        v_a_5950_ = crate::leanh::lean_ctor_get(v___x_5949_, 0);
                        crate::leanh::lean_inc(v_a_5950_);
                        crate::leanh::lean_dec_ref_known(v___x_5949_, 1);
                        v___x_5951_ = 1usize;
                        v___x_5952_ = lean_usize_add(v_i_5941_, v___x_5951_);
                        v_i_5941_ = v___x_5952_;
                        v_b_5943_ = v_a_5950_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_sp_5939_);
                        return v___x_5949_;
                    }
                } else {
                    crate::leanh::lean_dec(v_sp_5939_);
                    v___x_5954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5954_, 0, v_b_5943_);
                    return v___x_5954_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(
    mut v_useErrorFormat_5955_: *mut crate::leanh::LeanObject,
    mut v_sp_5956_: *mut crate::leanh::LeanObject,
    mut v_as_5957_: *mut crate::leanh::LeanObject,
    mut v_i_5958_: *mut crate::leanh::LeanObject,
    mut v_stop_5959_: *mut crate::leanh::LeanObject,
    mut v_b_5960_: *mut crate::leanh::LeanObject,
    mut v___y_5961_: *mut crate::leanh::LeanObject,
    mut v___y_5962_: *mut crate::leanh::LeanObject,
    mut v___y_5963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_5964_: u8 = 0;
    let mut v_i_boxed_5965_: usize = 0;
    let mut v_stop_boxed_5966_: usize = 0;
    let mut v_res_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_5964_ = (crate::leanh::lean_unbox(v_useErrorFormat_5955_) as u8);
    v_i_boxed_5965_ = crate::leanh::lean_unbox_usize(v_i_5958_);
    crate::leanh::lean_dec(v_i_5958_);
    v_stop_boxed_5966_ = crate::leanh::lean_unbox_usize(v_stop_5959_);
    crate::leanh::lean_dec(v_stop_5959_);
    v_res_5967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_boxed_5964_, v_sp_5956_, v_as_5957_, v_i_boxed_5965_, v_stop_boxed_5966_, v_b_5960_, v___y_5961_, v___y_5962_);
    crate::leanh::lean_dec(v___y_5962_);
    crate::leanh::lean_dec_ref(v___y_5961_);
    crate::leanh::lean_dec_ref(v_as_5957_);
    return v_res_5967_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(
    mut v_hi_5968_: *mut crate::leanh::LeanObject,
    mut v_pivot_5969_: *mut crate::leanh::LeanObject,
    mut v_as_5970_: *mut crate::leanh::LeanObject,
    mut v_i_5971_: *mut crate::leanh::LeanObject,
    mut v_k_5972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5973_: u8 = 0;
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5973_ = lean_nat_dec_lt(v_k_5972_, v_hi_5968_);
                if v___x_5973_ == 0 {
                    crate::leanh::lean_dec(v_k_5972_);
                    crate::leanh::lean_dec_ref(v_pivot_5969_);
                    v___x_5974_ = lean_array_fswap(v_as_5970_, v_i_5971_, v_hi_5968_);
                    v___x_5975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5975_, 0, v_i_5971_);
                    crate::leanh::lean_ctor_set(v___x_5975_, 1, v___x_5974_);
                    return v___x_5975_;
                } else {
                    v___x_5976_ = lean_array_fget_borrowed(v_as_5970_, v_k_5972_);
                    v_fst_5977_ = crate::leanh::lean_ctor_get(v___x_5976_, 0);
                    v_fst_5978_ = crate::leanh::lean_ctor_get(v_pivot_5969_, 0);
                    crate::leanh::lean_inc(v_fst_5977_);
                    v___x_5979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_fst_5977_,
                        v___x_5973_,
                    );
                    crate::leanh::lean_inc(v_fst_5978_);
                    v___x_5980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_fst_5978_,
                        v___x_5973_,
                    );
                    v___x_5981_ = lean_string_dec_lt(v___x_5979_, v___x_5980_);
                    crate::leanh::lean_dec_ref(v___x_5980_);
                    crate::leanh::lean_dec_ref(v___x_5979_);
                    if v___x_5981_ == 0 {
                        v___x_5982_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5983_ = lean_nat_add(v_k_5972_, v___x_5982_);
                        crate::leanh::lean_dec(v_k_5972_);
                        v_k_5972_ = v___x_5983_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5985_ = lean_array_fswap(v_as_5970_, v_i_5971_, v_k_5972_);
                        v___x_5986_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5987_ = lean_nat_add(v_i_5971_, v___x_5986_);
                        crate::leanh::lean_dec(v_i_5971_);
                        v___x_5988_ = lean_nat_add(v_k_5972_, v___x_5986_);
                        crate::leanh::lean_dec(v_k_5972_);
                        v_as_5970_ = v___x_5985_;
                        v_i_5971_ = v___x_5987_;
                        v_k_5972_ = v___x_5988_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(
    mut v_hi_5990_: *mut crate::leanh::LeanObject,
    mut v_pivot_5991_: *mut crate::leanh::LeanObject,
    mut v_as_5992_: *mut crate::leanh::LeanObject,
    mut v_i_5993_: *mut crate::leanh::LeanObject,
    mut v_k_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_5990_, v_pivot_5991_, v_as_5992_, v_i_5993_, v_k_5994_);
    crate::leanh::lean_dec(v_hi_5990_);
    return v_res_5995_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(
    mut v___x_5996_: u8,
    mut v_x_5997_: *mut crate::leanh::LeanObject,
    mut v_x_5998_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: u8 = 0;
    v_fst_5999_ = crate::leanh::lean_ctor_get(v_x_5997_, 0);
    crate::leanh::lean_inc(v_fst_5999_);
    crate::leanh::lean_dec_ref(v_x_5997_);
    v_fst_6000_ = crate::leanh::lean_ctor_get(v_x_5998_, 0);
    crate::leanh::lean_inc(v_fst_6000_);
    crate::leanh::lean_dec_ref(v_x_5998_);
    v___x_6001_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_5999_, v___x_5996_);
    v___x_6002_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_6000_, v___x_5996_);
    v___x_6003_ = lean_string_dec_lt(v___x_6001_, v___x_6002_);
    crate::leanh::lean_dec_ref(v___x_6002_);
    crate::leanh::lean_dec_ref(v___x_6001_);
    return v___x_6003_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(
    mut v___x_6004_: *mut crate::leanh::LeanObject,
    mut v_x_6005_: *mut crate::leanh::LeanObject,
    mut v_x_6006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5444__boxed_6007_: u8 = 0;
    let mut v_res_6008_: u8 = 0;
    let mut v_r_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5444__boxed_6007_ = (crate::leanh::lean_unbox(v___x_6004_) as u8);
    v_res_6008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_5444__boxed_6007_, v_x_6005_, v_x_6006_);
    v_r_6009_ = crate::leanh::lean_box((v_res_6008_) as usize);
    return v_r_6009_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(
    mut v_n_6010_: *mut crate::leanh::LeanObject,
    mut v_as_6011_: *mut crate::leanh::LeanObject,
    mut v_lo_6012_: *mut crate::leanh::LeanObject,
    mut v_hi_6013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: u8 = 0;
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: u8 = 0;
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: u8 = 0;
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: u8 = 0;
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: u8 = 0;
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6025_ = lean_nat_dec_lt(v_lo_6012_, v_hi_6013_);
                if v___x_6025_ == 0 {
                    crate::leanh::lean_dec(v_lo_6012_);
                    return v_as_6011_;
                } else {
                    v___x_6026_ = lean_nat_add(v_lo_6012_, v_hi_6013_);
                    v___x_6027_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_6028_ = lean_nat_shiftr(v___x_6026_, v___x_6027_);
                    crate::leanh::lean_dec(v___x_6026_);
                    v___x_6041_ = lean_array_fget_borrowed(v_as_6011_, v_mid_6028_);
                    v___x_6042_ = lean_array_fget_borrowed(v_as_6011_, v_lo_6012_);
                    crate::leanh::lean_inc(v___x_6042_);
                    crate::leanh::lean_inc(v___x_6041_);
                    v___x_6043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_6025_, v___x_6041_, v___x_6042_);
                    if v___x_6043_ == 0 {
                        v___y_6036_ = v_as_6011_;
                        state = 3;
                        continue;
                    } else {
                        v___x_6044_ = lean_array_fswap(v_as_6011_, v_lo_6012_, v_mid_6028_);
                        v___y_6036_ = v___x_6044_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_6016_ = lean_array_fget(v___y_6015_, v_hi_6013_);
                crate::leanh::lean_inc_n(v_lo_6012_, 2);
                v___x_6017_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_6013_, v_pivot_6016_, v___y_6015_, v_lo_6012_, v_lo_6012_);
                v_fst_6018_ = crate::leanh::lean_ctor_get(v___x_6017_, 0);
                crate::leanh::lean_inc(v_fst_6018_);
                v_snd_6019_ = crate::leanh::lean_ctor_get(v___x_6017_, 1);
                crate::leanh::lean_inc(v_snd_6019_);
                crate::leanh::lean_dec_ref(v___x_6017_);
                v___x_6020_ = lean_nat_dec_le(v_hi_6013_, v_fst_6018_);
                if v___x_6020_ == 0 {
                    v___x_6021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_6010_, v_snd_6019_, v_lo_6012_, v_fst_6018_);
                    v___x_6022_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6023_ = lean_nat_add(v_fst_6018_, v___x_6022_);
                    crate::leanh::lean_dec(v_fst_6018_);
                    v_as_6011_ = v___x_6021_;
                    v_lo_6012_ = v___x_6023_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_6018_);
                    crate::leanh::lean_dec(v_lo_6012_);
                    return v_snd_6019_;
                }
            }
            2 => {
                v___x_6031_ = lean_array_fget_borrowed(v___y_6030_, v_mid_6028_);
                v___x_6032_ = lean_array_fget_borrowed(v___y_6030_, v_hi_6013_);
                crate::leanh::lean_inc(v___x_6032_);
                crate::leanh::lean_inc(v___x_6031_);
                v___x_6033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_6025_, v___x_6031_, v___x_6032_);
                if v___x_6033_ == 0 {
                    crate::leanh::lean_dec(v_mid_6028_);
                    v___y_6015_ = v___y_6030_;
                    state = 1;
                    continue;
                } else {
                    v___x_6034_ = lean_array_fswap(v___y_6030_, v_mid_6028_, v_hi_6013_);
                    crate::leanh::lean_dec(v_mid_6028_);
                    v___y_6015_ = v___x_6034_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6037_ = lean_array_fget_borrowed(v___y_6036_, v_hi_6013_);
                v___x_6038_ = lean_array_fget_borrowed(v___y_6036_, v_lo_6012_);
                crate::leanh::lean_inc(v___x_6038_);
                crate::leanh::lean_inc(v___x_6037_);
                v___x_6039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_6025_, v___x_6037_, v___x_6038_);
                if v___x_6039_ == 0 {
                    v___y_6030_ = v___y_6036_;
                    state = 2;
                    continue;
                } else {
                    v___x_6040_ = lean_array_fswap(v___y_6036_, v_lo_6012_, v_hi_6013_);
                    v___y_6030_ = v___x_6040_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(
    mut v_n_6045_: *mut crate::leanh::LeanObject,
    mut v_as_6046_: *mut crate::leanh::LeanObject,
    mut v_lo_6047_: *mut crate::leanh::LeanObject,
    mut v_hi_6048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_6045_, v_as_6046_, v_lo_6047_, v_hi_6048_);
    crate::leanh::lean_dec(v_hi_6048_);
    crate::leanh::lean_dec(v_n_6045_);
    return v_res_6049_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6050_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarnings___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarnings___closed__0_once),
        _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0,
    );
    v___x_6051_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6051_, 0, v___x_6050_);
    crate::leanh::lean_ctor_set(v___x_6051_, 1, v___x_6050_);
    return v___x_6051_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_groupedByFilename(
    mut v_results_6052_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_6053_: u8,
    mut v_a_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6067_: u8 = 0;
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_a_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6081_: u8 = 0;
    let mut v___y_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: u8 = 0;
    let mut v___y_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: u8 = 0;
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: u8 = 0;
    let mut v___y_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: u8 = 0;
    let mut v___x_6117_: u8 = 0;
    let mut v___x_6118_: usize = 0;
    let mut v___x_6119_: usize = 0;
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: usize = 0;
    let mut v___x_6122_: usize = 0;
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6134_: u8 = 0;
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_sp_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: u8 = 0;
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: u8 = 0;
    let mut v___x_6150_: usize = 0;
    let mut v___x_6151_: usize = 0;
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: usize = 0;
    let mut v___x_6154_: usize = 0;
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6162_: u8 = 0;
    let mut v_ref_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useErrorFormat_6053_ == 0 {
                    v___x_6156_ = crate::leanh::lean_box(0);
                    v_sp_6140_ = v___x_6156_;
                    v___y_6141_ = v_a_6054_;
                    v___y_6142_ = v_a_6055_;
                    state = 13;
                    continue;
                } else {
                    v___x_6157_ = l_Lean_getSrcSearchPath();
                    if crate::leanh::lean_obj_tag(v___x_6157_) == 0 {
                        v_a_6158_ = crate::leanh::lean_ctor_get(v___x_6157_, 0);
                        crate::leanh::lean_inc(v_a_6158_);
                        crate::leanh::lean_dec_ref_known(v___x_6157_, 1);
                        v_sp_6140_ = v_a_6158_;
                        v___y_6141_ = v_a_6054_;
                        v___y_6142_ = v_a_6055_;
                        state = 13;
                        continue;
                    } else {
                        v_a_6159_ = crate::leanh::lean_ctor_get(v___x_6157_, 0);
                        v_isSharedCheck_6171_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6157_)) as u8;
                        if v_isSharedCheck_6171_ == 0 {
                            v___x_6161_ = v___x_6157_;
                            v_isShared_6162_ = v_isSharedCheck_6171_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6159_);
                            crate::leanh::lean_dec(v___x_6157_);
                            v___x_6161_ = crate::leanh::lean_box(0);
                            v_isShared_6162_ = v_isSharedCheck_6171_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6061_ = lean_array_to_list(v___y_6060_);
                v___x_6062_ = crate::leanh::lean_box(0);
                v___x_6063_ =
                    l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(
                        v_useErrorFormat_6053_,
                        v___x_6061_,
                        v___x_6062_,
                        v___y_6058_,
                        v___y_6059_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6063_) == 0 {
                    v_a_6064_ = crate::leanh::lean_ctor_get(v___x_6063_, 0);
                    v_isSharedCheck_6073_ = (!crate::leanh::lean_is_exclusive(v___x_6063_)) as u8;
                    if v_isSharedCheck_6073_ == 0 {
                        v___x_6066_ = v___x_6063_;
                        v_isShared_6067_ = v_isSharedCheck_6073_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6064_);
                        crate::leanh::lean_dec(v___x_6063_);
                        v___x_6066_ = crate::leanh::lean_box(0);
                        v_isShared_6067_ = v_isSharedCheck_6073_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6074_ = crate::leanh::lean_ctor_get(v___x_6063_, 0);
                    v_isSharedCheck_6081_ = (!crate::leanh::lean_is_exclusive(v___x_6063_)) as u8;
                    if v_isSharedCheck_6081_ == 0 {
                        v___x_6076_ = v___x_6063_;
                        v_isShared_6077_ = v_isSharedCheck_6081_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6074_);
                        crate::leanh::lean_dec(v___x_6063_);
                        v___x_6076_ = crate::leanh::lean_box(0);
                        v_isShared_6077_ = v_isSharedCheck_6081_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6068_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_groupedByFilename___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0,
                );
                v___x_6069_ = l_Lean_MessageData_joinSep(v_a_6064_, v___x_6068_);
                if v_isShared_6067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6066_, 0, v___x_6069_);
                    v___x_6071_ = v___x_6066_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v___x_6069_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6071_;
            }
            4 => {
                if v_isShared_6077_ == 0 {
                    v___x_6079_ = v___x_6076_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6080_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
                    v___x_6079_ = v_reuseFailAlloc_6080_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6079_;
            }
            6 => {
                v___x_6089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v___y_6086_, v___y_6087_, v___y_6084_, v___y_6088_);
                crate::leanh::lean_dec(v___y_6088_);
                crate::leanh::lean_dec(v___y_6086_);
                v___y_6058_ = v___y_6083_;
                v___y_6059_ = v___y_6085_;
                v___y_6060_ = v___x_6089_;
                state = 1;
                continue;
            }
            7 => {
                v___x_6097_ = lean_nat_dec_le(v___y_6096_, v___y_6091_);
                if v___x_6097_ == 0 {
                    crate::leanh::lean_dec(v___y_6091_);
                    crate::leanh::lean_inc(v___y_6096_);
                    v___y_6083_ = v___y_6092_;
                    v___y_6084_ = v___y_6096_;
                    v___y_6085_ = v___y_6093_;
                    v___y_6086_ = v___y_6094_;
                    v___y_6087_ = v___y_6095_;
                    v___y_6088_ = v___y_6096_;
                    state = 6;
                    continue;
                } else {
                    v___y_6083_ = v___y_6092_;
                    v___y_6084_ = v___y_6096_;
                    v___y_6085_ = v___y_6093_;
                    v___y_6086_ = v___y_6094_;
                    v___y_6087_ = v___y_6095_;
                    v___y_6088_ = v___y_6091_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_6102_ = lean_array_get_size(v___y_6101_);
                v___x_6103_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6104_ = lean_nat_dec_eq(v___x_6102_, v___x_6103_);
                if v___x_6104_ == 0 {
                    v___x_6105_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6106_ = lean_nat_sub(v___x_6102_, v___x_6105_);
                    v___x_6107_ = lean_nat_dec_le(v___x_6103_, v___x_6106_);
                    if v___x_6107_ == 0 {
                        crate::leanh::lean_inc(v___x_6106_);
                        v___y_6091_ = v___x_6106_;
                        v___y_6092_ = v___y_6099_;
                        v___y_6093_ = v___y_6100_;
                        v___y_6094_ = v___x_6102_;
                        v___y_6095_ = v___y_6101_;
                        v___y_6096_ = v___x_6106_;
                        state = 7;
                        continue;
                    } else {
                        v___y_6091_ = v___x_6106_;
                        v___y_6092_ = v___y_6099_;
                        v___y_6093_ = v___y_6100_;
                        v___y_6094_ = v___x_6102_;
                        v___y_6095_ = v___y_6101_;
                        v___y_6096_ = v___x_6103_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_6058_ = v___y_6099_;
                    v___y_6059_ = v___y_6100_;
                    v___y_6060_ = v___y_6101_;
                    state = 1;
                    continue;
                }
            }
            9 => {
                v___x_6113_ = lean_mk_empty_array_with_capacity(v_size_6111_);
                crate::leanh::lean_dec(v_size_6111_);
                v___x_6114_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6115_ = lean_array_get_size(v_buckets_6112_);
                v___x_6116_ = lean_nat_dec_lt(v___x_6114_, v___x_6115_);
                if v___x_6116_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_6112_);
                    v___y_6099_ = v___y_6109_;
                    v___y_6100_ = v___y_6110_;
                    v___y_6101_ = v___x_6113_;
                    state = 8;
                    continue;
                } else {
                    v___x_6117_ = lean_nat_dec_le(v___x_6115_, v___x_6115_);
                    if v___x_6117_ == 0 {
                        if v___x_6116_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_6112_);
                            v___y_6099_ = v___y_6109_;
                            v___y_6100_ = v___y_6110_;
                            v___y_6101_ = v___x_6113_;
                            state = 8;
                            continue;
                        } else {
                            v___x_6118_ = 0usize;
                            v___x_6119_ = lean_usize_of_nat(v___x_6115_);
                            v___x_6120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_6112_, v___x_6118_, v___x_6119_, v___x_6113_);
                            crate::leanh::lean_dec_ref(v_buckets_6112_);
                            v___y_6099_ = v___y_6109_;
                            v___y_6100_ = v___y_6110_;
                            v___y_6101_ = v___x_6120_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_6121_ = 0usize;
                        v___x_6122_ = lean_usize_of_nat(v___x_6115_);
                        v___x_6123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_6112_, v___x_6121_, v___x_6122_, v___x_6113_);
                        crate::leanh::lean_dec_ref(v_buckets_6112_);
                        v___y_6099_ = v___y_6109_;
                        v___y_6100_ = v___y_6110_;
                        v___y_6101_ = v___x_6123_;
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v___y_6127_) == 0 {
                    v_a_6128_ = crate::leanh::lean_ctor_get(v___y_6127_, 0);
                    crate::leanh::lean_inc(v_a_6128_);
                    crate::leanh::lean_dec_ref_known(v___y_6127_, 1);
                    v_size_6129_ = crate::leanh::lean_ctor_get(v_a_6128_, 0);
                    crate::leanh::lean_inc(v_size_6129_);
                    v_buckets_6130_ = crate::leanh::lean_ctor_get(v_a_6128_, 1);
                    crate::leanh::lean_inc_ref(v_buckets_6130_);
                    crate::leanh::lean_dec(v_a_6128_);
                    v___y_6109_ = v___y_6125_;
                    v___y_6110_ = v___y_6126_;
                    v_size_6111_ = v_size_6129_;
                    v_buckets_6112_ = v_buckets_6130_;
                    state = 9;
                    continue;
                } else {
                    v_a_6131_ = crate::leanh::lean_ctor_get(v___y_6127_, 0);
                    v_isSharedCheck_6138_ = (!crate::leanh::lean_is_exclusive(v___y_6127_)) as u8;
                    if v_isSharedCheck_6138_ == 0 {
                        v___x_6133_ = v___y_6127_;
                        v_isShared_6134_ = v_isSharedCheck_6138_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6131_);
                        crate::leanh::lean_dec(v___y_6127_);
                        v___x_6133_ = crate::leanh::lean_box(0);
                        v_isShared_6134_ = v_isSharedCheck_6138_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_6134_ == 0 {
                    v___x_6136_ = v___x_6133_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_a_6131_);
                    v___x_6136_ = v_reuseFailAlloc_6137_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6136_;
            }
            13 => {
                v_buckets_6143_ = crate::leanh::lean_ctor_get(v_results_6052_, 1);
                v___x_6144_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6145_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
                v___x_6146_ = lean_array_get_size(v_buckets_6143_);
                v___x_6147_ = lean_nat_dec_lt(v___x_6144_, v___x_6146_);
                if v___x_6147_ == 0 {
                    crate::leanh::lean_dec(v_sp_6140_);
                    v___y_6109_ = v___y_6141_;
                    v___y_6110_ = v___y_6142_;
                    v_size_6111_ = v___x_6144_;
                    v_buckets_6112_ = v___x_6145_;
                    state = 9;
                    continue;
                } else {
                    v___x_6148_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
                    v___x_6149_ = lean_nat_dec_le(v___x_6146_, v___x_6146_);
                    if v___x_6149_ == 0 {
                        if v___x_6147_ == 0 {
                            crate::leanh::lean_dec(v_sp_6140_);
                            v___y_6109_ = v___y_6141_;
                            v___y_6110_ = v___y_6142_;
                            v_size_6111_ = v___x_6144_;
                            v_buckets_6112_ = v___x_6145_;
                            state = 9;
                            continue;
                        } else {
                            v___x_6150_ = 0usize;
                            v___x_6151_ = lean_usize_of_nat(v___x_6146_);
                            v___x_6152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_6053_, v_sp_6140_, v_buckets_6143_, v___x_6150_, v___x_6151_, v___x_6148_, v___y_6141_, v___y_6142_);
                            v___y_6125_ = v___y_6141_;
                            v___y_6126_ = v___y_6142_;
                            v___y_6127_ = v___x_6152_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_6153_ = 0usize;
                        v___x_6154_ = lean_usize_of_nat(v___x_6146_);
                        v___x_6155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_6053_, v_sp_6140_, v_buckets_6143_, v___x_6153_, v___x_6154_, v___x_6148_, v___y_6141_, v___y_6142_);
                        v___y_6125_ = v___y_6141_;
                        v___y_6126_ = v___y_6142_;
                        v___y_6127_ = v___x_6155_;
                        state = 10;
                        continue;
                    }
                }
            }
            14 => {
                v_ref_6163_ = crate::leanh::lean_ctor_get(v_a_6054_, 5);
                v___x_6164_ = lean_io_error_to_string(v_a_6159_);
                v___x_6165_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6165_, 0, v___x_6164_);
                v___x_6166_ = l_Lean_MessageData_ofFormat(v___x_6165_);
                crate::leanh::lean_inc(v_ref_6163_);
                v___x_6167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6167_, 0, v_ref_6163_);
                crate::leanh::lean_ctor_set(v___x_6167_, 1, v___x_6166_);
                if v_isShared_6162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6161_, 0, v___x_6167_);
                    v___x_6169_ = v___x_6161_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6170_, 0, v___x_6167_);
                    v___x_6169_ = v_reuseFailAlloc_6170_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_groupedByFilename___boxed(
    mut v_results_6172_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_6173_: *mut crate::leanh::LeanObject,
    mut v_a_6174_: *mut crate::leanh::LeanObject,
    mut v_a_6175_: *mut crate::leanh::LeanObject,
    mut v_a_6176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_6177_: u8 = 0;
    let mut v_res_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_6177_ = (crate::leanh::lean_unbox(v_useErrorFormat_6173_) as u8);
    v_res_6178_ = l_Lean_Linter_EnvLinter_groupedByFilename(
        v_results_6172_,
        v_useErrorFormat_boxed_6177_,
        v_a_6174_,
        v_a_6175_,
    );
    crate::leanh::lean_dec(v_a_6175_);
    crate::leanh::lean_dec_ref(v_a_6174_);
    crate::leanh::lean_dec_ref(v_results_6172_);
    return v_res_6178_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(
    mut v_n_6179_: *mut crate::leanh::LeanObject,
    mut v_as_6180_: *mut crate::leanh::LeanObject,
    mut v_lo_6181_: *mut crate::leanh::LeanObject,
    mut v_hi_6182_: *mut crate::leanh::LeanObject,
    mut v_w_6183_: *mut crate::leanh::LeanObject,
    mut v_hlo_6184_: *mut crate::leanh::LeanObject,
    mut v_hhi_6185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_6179_, v_as_6180_, v_lo_6181_, v_hi_6182_);
    return v___x_6186_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(
    mut v_n_6187_: *mut crate::leanh::LeanObject,
    mut v_as_6188_: *mut crate::leanh::LeanObject,
    mut v_lo_6189_: *mut crate::leanh::LeanObject,
    mut v_hi_6190_: *mut crate::leanh::LeanObject,
    mut v_w_6191_: *mut crate::leanh::LeanObject,
    mut v_hlo_6192_: *mut crate::leanh::LeanObject,
    mut v_hhi_6193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6194_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(v_n_6187_, v_as_6188_, v_lo_6189_, v_hi_6190_, v_w_6191_, v_hlo_6192_, v_hhi_6193_);
    crate::leanh::lean_dec(v_hi_6190_);
    crate::leanh::lean_dec(v_n_6187_);
    return v_res_6194_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(
    mut v_00_u03b2_6195_: *mut crate::leanh::LeanObject,
    mut v_m_6196_: *mut crate::leanh::LeanObject,
    mut v_a_6197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6198_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_6196_, v_a_6197_);
    return v___x_6198_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(
    mut v_00_u03b2_6199_: *mut crate::leanh::LeanObject,
    mut v_m_6200_: *mut crate::leanh::LeanObject,
    mut v_a_6201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(v_00_u03b2_6199_, v_m_6200_, v_a_6201_);
    crate::leanh::lean_dec(v_a_6201_);
    crate::leanh::lean_dec_ref(v_m_6200_);
    return v_res_6202_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(
    mut v_n_6203_: *mut crate::leanh::LeanObject,
    mut v_lo_6204_: *mut crate::leanh::LeanObject,
    mut v_hi_6205_: *mut crate::leanh::LeanObject,
    mut v_hhi_6206_: *mut crate::leanh::LeanObject,
    mut v_pivot_6207_: *mut crate::leanh::LeanObject,
    mut v_as_6208_: *mut crate::leanh::LeanObject,
    mut v_i_6209_: *mut crate::leanh::LeanObject,
    mut v_k_6210_: *mut crate::leanh::LeanObject,
    mut v_ilo_6211_: *mut crate::leanh::LeanObject,
    mut v_ik_6212_: *mut crate::leanh::LeanObject,
    mut v_w_6213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6214_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_6205_, v_pivot_6207_, v_as_6208_, v_i_6209_, v_k_6210_);
    return v___x_6214_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(
    mut v_n_6215_: *mut crate::leanh::LeanObject,
    mut v_lo_6216_: *mut crate::leanh::LeanObject,
    mut v_hi_6217_: *mut crate::leanh::LeanObject,
    mut v_hhi_6218_: *mut crate::leanh::LeanObject,
    mut v_pivot_6219_: *mut crate::leanh::LeanObject,
    mut v_as_6220_: *mut crate::leanh::LeanObject,
    mut v_i_6221_: *mut crate::leanh::LeanObject,
    mut v_k_6222_: *mut crate::leanh::LeanObject,
    mut v_ilo_6223_: *mut crate::leanh::LeanObject,
    mut v_ik_6224_: *mut crate::leanh::LeanObject,
    mut v_w_6225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(v_n_6215_, v_lo_6216_, v_hi_6217_, v_hhi_6218_, v_pivot_6219_, v_as_6220_, v_i_6221_, v_k_6222_, v_ilo_6223_, v_ik_6224_, v_w_6225_);
    crate::leanh::lean_dec(v_hi_6217_);
    crate::leanh::lean_dec(v_lo_6216_);
    crate::leanh::lean_dec(v_n_6215_);
    return v_res_6226_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(
    mut v_00_u03b2_6227_: *mut crate::leanh::LeanObject,
    mut v_a_6228_: *mut crate::leanh::LeanObject,
    mut v_x_6229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_6228_, v_x_6229_);
    return v___x_6230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(
    mut v_00_u03b2_6231_: *mut crate::leanh::LeanObject,
    mut v_a_6232_: *mut crate::leanh::LeanObject,
    mut v_x_6233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(v_00_u03b2_6231_, v_a_6232_, v_x_6233_);
    crate::leanh::lean_dec(v_x_6233_);
    crate::leanh::lean_dec(v_a_6232_);
    return v_res_6234_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(
    mut v_sz_6235_: usize,
    mut v_i_6236_: usize,
    mut v_bs_6237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6238_: u8 = 0;
    let mut v_v_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: usize = 0;
    let mut v___x_6245_: usize = 0;
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6238_ = lean_usize_dec_lt(v_i_6236_, v_sz_6235_);
                if v___x_6238_ == 0 {
                    return v_bs_6237_;
                } else {
                    v_v_6239_ = lean_array_uget_borrowed(v_bs_6237_, v_i_6236_);
                    v_snd_6240_ = crate::leanh::lean_ctor_get(v_v_6239_, 1);
                    v_size_6241_ = crate::leanh::lean_ctor_get(v_snd_6240_, 0);
                    crate::leanh::lean_inc(v_size_6241_);
                    v___x_6242_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6243_ = lean_array_uset(v_bs_6237_, v_i_6236_, v___x_6242_);
                    v___x_6244_ = 1usize;
                    v___x_6245_ = lean_usize_add(v_i_6236_, v___x_6244_);
                    v___x_6246_ = lean_array_uset(v_bs_x27_6243_, v_i_6236_, v_size_6241_);
                    v_i_6236_ = v___x_6245_;
                    v_bs_6237_ = v___x_6246_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(
    mut v_sz_6248_: *mut crate::leanh::LeanObject,
    mut v_i_6249_: *mut crate::leanh::LeanObject,
    mut v_bs_6250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6251_: usize = 0;
    let mut v_i_boxed_6252_: usize = 0;
    let mut v_res_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6251_ = crate::leanh::lean_unbox_usize(v_sz_6248_);
    crate::leanh::lean_dec(v_sz_6248_);
    v_i_boxed_6252_ = crate::leanh::lean_unbox_usize(v_i_6249_);
    crate::leanh::lean_dec(v_i_6249_);
    v_res_6253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_boxed_6251_, v_i_boxed_6252_, v_bs_6250_);
    return v_res_6253_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0;
    v___x_6256_ = l_Lean_stringToMessageData(v___x_6255_);
    return v___x_6256_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2;
    v___x_6259_ = l_Lean_stringToMessageData(v___x_6258_);
    return v___x_6259_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4;
    v___x_6262_ = l_Lean_stringToMessageData(v___x_6261_);
    return v___x_6262_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6;
    v___x_6265_ = l_Lean_stringToMessageData(v___x_6264_);
    return v___x_6265_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(
    mut v_useErrorFormat_6266_: u8,
    mut v_groupByFilename_6267_: u8,
    mut v_verbose_6268_: u8,
    mut v_as_6269_: *mut crate::leanh::LeanObject,
    mut v_i_6270_: usize,
    mut v_stop_6271_: usize,
    mut v_b_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: usize = 0;
    let mut v___x_6279_: usize = 0;
    let mut v_val_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: u8 = 0;
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6290_: u8 = 0;
    let mut v_warnings_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvLinter_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorsFound_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut v_size_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: u8 = 0;
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6329_: u8 = 0;
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6333_: u8 = 0;
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v___x_6337_: u8 = 0;
    let mut v___x_6338_: u8 = 0;
    let mut v_toEnvLinter_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noErrorsFound_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6347_: u8 = 0;
    let mut v_unused_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6350_: u8 = 0;
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6284_ = lean_usize_dec_eq(v_i_6270_, v_stop_6271_);
                if v___x_6284_ == 0 {
                    v___x_6285_ = lean_array_uget(v_as_6269_, v_i_6270_);
                    v_fst_6286_ = crate::leanh::lean_ctor_get(v___x_6285_, 0);
                    v_snd_6287_ = crate::leanh::lean_ctor_get(v___x_6285_, 1);
                    v_isSharedCheck_6350_ = (!crate::leanh::lean_is_exclusive(v___x_6285_)) as u8;
                    if v_isSharedCheck_6350_ == 0 {
                        v___x_6289_ = v___x_6285_;
                        v_isShared_6290_ = v_isSharedCheck_6350_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6287_);
                        crate::leanh::lean_inc(v_fst_6286_);
                        crate::leanh::lean_dec(v___x_6285_);
                        v___x_6289_ = crate::leanh::lean_box(0);
                        v_isShared_6290_ = v_isSharedCheck_6350_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6351_, 0, v_b_6272_);
                    return v___x_6351_;
                }
            }
            1 => {
                v___x_6278_ = 1usize;
                v___x_6279_ = lean_usize_add(v_i_6270_, v___x_6278_);
                v_i_6270_ = v___x_6279_;
                v_b_6272_ = v_a_6277_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6283_ = lean_array_push(v_b_6272_, v_val_6282_);
                v_a_6277_ = v___x_6283_;
                state = 1;
                continue;
            }
            3 => {
                v_size_6320_ = crate::leanh::lean_ctor_get(v_snd_6287_, 0);
                v___x_6321_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6322_ = lean_nat_dec_eq(v_size_6320_, v___x_6321_);
                if v___x_6322_ == 0 {
                    if v_groupByFilename_6267_ == 0 {
                        if v_useErrorFormat_6266_ == 0 {
                            v___x_6323_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0;
                            v___x_6324_ = l_Lean_Linter_EnvLinter_printWarnings(
                                v_snd_6287_,
                                v___x_6323_,
                                v_useErrorFormat_6266_,
                                v___y_6273_,
                                v___y_6274_,
                            );
                            crate::leanh::lean_dec(v_snd_6287_);
                            if crate::leanh::lean_obj_tag(v___x_6324_) == 0 {
                                v_a_6325_ = crate::leanh::lean_ctor_get(v___x_6324_, 0);
                                crate::leanh::lean_inc(v_a_6325_);
                                crate::leanh::lean_dec_ref_known(v___x_6324_, 1);
                                v_warnings_6292_ = v_a_6325_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_6289_);
                                crate::leanh::lean_dec(v_fst_6286_);
                                crate::leanh::lean_dec_ref(v_b_6272_);
                                v_a_6326_ = crate::leanh::lean_ctor_get(v___x_6324_, 0);
                                v_isSharedCheck_6333_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6324_)) as u8;
                                if v_isSharedCheck_6333_ == 0 {
                                    v___x_6328_ = v___x_6324_;
                                    v_isShared_6329_ = v_isSharedCheck_6333_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6326_);
                                    crate::leanh::lean_dec(v___x_6324_);
                                    v___x_6328_ = crate::leanh::lean_box(0);
                                    v_isShared_6329_ = v_isSharedCheck_6333_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            state = 6;
                            continue;
                        }
                    } else {
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6289_);
                    v_isSharedCheck_6347_ = (!crate::leanh::lean_is_exclusive(v_snd_6287_)) as u8;
                    if v_isSharedCheck_6347_ == 0 {
                        v_unused_6348_ = crate::leanh::lean_ctor_get(v_snd_6287_, 1);
                        crate::leanh::lean_dec(v_unused_6348_);
                        v_unused_6349_ = crate::leanh::lean_ctor_get(v_snd_6287_, 0);
                        crate::leanh::lean_dec(v_unused_6349_);
                        v___x_6335_ = v_snd_6287_;
                        v_isShared_6336_ = v_isSharedCheck_6347_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_6287_);
                        v___x_6335_ = crate::leanh::lean_box(0);
                        v_isShared_6336_ = v_isSharedCheck_6347_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v_toEnvLinter_6293_ = crate::leanh::lean_ctor_get(v_fst_6286_, 0);
                crate::leanh::lean_inc_ref(v_toEnvLinter_6293_);
                v_name_6294_ = crate::leanh::lean_ctor_get(v_fst_6286_, 1);
                crate::leanh::lean_inc(v_name_6294_);
                crate::leanh::lean_dec(v_fst_6286_);
                v_errorsFound_6295_ = crate::leanh::lean_ctor_get(v_toEnvLinter_6293_, 2);
                crate::leanh::lean_inc_ref(v_errorsFound_6295_);
                crate::leanh::lean_dec_ref(v_toEnvLinter_6293_);
                v___x_6296_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1);
                v___x_6297_ = l_Lean_MessageData_ofName(v_name_6294_);
                if v_isShared_6290_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6289_, 7);
                    crate::leanh::lean_ctor_set(v___x_6289_, 1, v___x_6297_);
                    crate::leanh::lean_ctor_set(v___x_6289_, 0, v___x_6296_);
                    v___x_6299_ = v___x_6289_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6308_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6308_, 0, v___x_6296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6308_, 1, v___x_6297_);
                    v___x_6299_ = v_reuseFailAlloc_6308_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6300_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3);
                v___x_6301_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6301_, 0, v___x_6299_);
                crate::leanh::lean_ctor_set(v___x_6301_, 1, v___x_6300_);
                v___x_6302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6302_, 0, v___x_6301_);
                crate::leanh::lean_ctor_set(v___x_6302_, 1, v_errorsFound_6295_);
                v___x_6303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5);
                v___x_6304_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6304_, 0, v___x_6302_);
                crate::leanh::lean_ctor_set(v___x_6304_, 1, v___x_6303_);
                v___x_6305_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6305_, 0, v___x_6304_);
                crate::leanh::lean_ctor_set(v___x_6305_, 1, v_warnings_6292_);
                v___x_6306_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3), core::ptr::addr_of_mut!(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once), _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
                v___x_6307_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6307_, 0, v___x_6305_);
                crate::leanh::lean_ctor_set(v___x_6307_, 1, v___x_6306_);
                v_val_6282_ = v___x_6307_;
                state = 2;
                continue;
            }
            6 => {
                v___x_6310_ = l_Lean_Linter_EnvLinter_groupedByFilename(
                    v_snd_6287_,
                    v_useErrorFormat_6266_,
                    v___y_6273_,
                    v___y_6274_,
                );
                crate::leanh::lean_dec(v_snd_6287_);
                if crate::leanh::lean_obj_tag(v___x_6310_) == 0 {
                    v_a_6311_ = crate::leanh::lean_ctor_get(v___x_6310_, 0);
                    crate::leanh::lean_inc(v_a_6311_);
                    crate::leanh::lean_dec_ref_known(v___x_6310_, 1);
                    v_warnings_6292_ = v_a_6311_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_6289_);
                    crate::leanh::lean_dec(v_fst_6286_);
                    crate::leanh::lean_dec_ref(v_b_6272_);
                    v_a_6312_ = crate::leanh::lean_ctor_get(v___x_6310_, 0);
                    v_isSharedCheck_6319_ = (!crate::leanh::lean_is_exclusive(v___x_6310_)) as u8;
                    if v_isSharedCheck_6319_ == 0 {
                        v___x_6314_ = v___x_6310_;
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6312_);
                        crate::leanh::lean_dec(v___x_6310_);
                        v___x_6314_ = crate::leanh::lean_box(0);
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_6315_ == 0 {
                    v___x_6317_ = v___x_6314_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
                    v___x_6317_ = v_reuseFailAlloc_6318_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6317_;
            }
            9 => {
                if v_isShared_6329_ == 0 {
                    v___x_6331_ = v___x_6328_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6332_, 0, v_a_6326_);
                    v___x_6331_ = v_reuseFailAlloc_6332_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6331_;
            }
            11 => {
                v___x_6337_ = 2;
                v___x_6338_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(
                    v_verbose_6268_,
                    v___x_6337_,
                );
                if v___x_6338_ == 0 {
                    crate::leanh::lean_del_object(v___x_6335_);
                    crate::leanh::lean_dec(v_fst_6286_);
                    v_a_6277_ = v_b_6272_;
                    state = 1;
                    continue;
                } else {
                    v_toEnvLinter_6339_ = crate::leanh::lean_ctor_get(v_fst_6286_, 0);
                    crate::leanh::lean_inc_ref(v_toEnvLinter_6339_);
                    crate::leanh::lean_dec(v_fst_6286_);
                    v_noErrorsFound_6340_ = crate::leanh::lean_ctor_get(v_toEnvLinter_6339_, 1);
                    crate::leanh::lean_inc_ref(v_noErrorsFound_6340_);
                    crate::leanh::lean_dec_ref(v_toEnvLinter_6339_);
                    v___x_6341_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7);
                    if v_isShared_6336_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6335_, 7);
                        crate::leanh::lean_ctor_set(v___x_6335_, 1, v_noErrorsFound_6340_);
                        crate::leanh::lean_ctor_set(v___x_6335_, 0, v___x_6341_);
                        v___x_6343_ = v___x_6335_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_6346_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6346_, 0, v___x_6341_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_6346_,
                            1,
                            v_noErrorsFound_6340_,
                        );
                        v___x_6343_ = v_reuseFailAlloc_6346_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                v___x_6344_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarning___closed__5_once),
                    _init_l_Lean_Linter_EnvLinter_printWarning___closed__5,
                );
                v___x_6345_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6345_, 0, v___x_6343_);
                crate::leanh::lean_ctor_set(v___x_6345_, 1, v___x_6344_);
                v_val_6282_ = v___x_6345_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(
    mut v_useErrorFormat_6352_: *mut crate::leanh::LeanObject,
    mut v_groupByFilename_6353_: *mut crate::leanh::LeanObject,
    mut v_verbose_6354_: *mut crate::leanh::LeanObject,
    mut v_as_6355_: *mut crate::leanh::LeanObject,
    mut v_i_6356_: *mut crate::leanh::LeanObject,
    mut v_stop_6357_: *mut crate::leanh::LeanObject,
    mut v_b_6358_: *mut crate::leanh::LeanObject,
    mut v___y_6359_: *mut crate::leanh::LeanObject,
    mut v___y_6360_: *mut crate::leanh::LeanObject,
    mut v___y_6361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_6362_: u8 = 0;
    let mut v_groupByFilename_boxed_6363_: u8 = 0;
    let mut v_verbose_boxed_6364_: u8 = 0;
    let mut v_i_boxed_6365_: usize = 0;
    let mut v_stop_boxed_6366_: usize = 0;
    let mut v_res_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_6362_ = (crate::leanh::lean_unbox(v_useErrorFormat_6352_) as u8);
    v_groupByFilename_boxed_6363_ = (crate::leanh::lean_unbox(v_groupByFilename_6353_) as u8);
    v_verbose_boxed_6364_ = (crate::leanh::lean_unbox(v_verbose_6354_) as u8);
    v_i_boxed_6365_ = crate::leanh::lean_unbox_usize(v_i_6356_);
    crate::leanh::lean_dec(v_i_6356_);
    v_stop_boxed_6366_ = crate::leanh::lean_unbox_usize(v_stop_6357_);
    crate::leanh::lean_dec(v_stop_6357_);
    v_res_6367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_boxed_6362_, v_groupByFilename_boxed_6363_, v_verbose_boxed_6364_, v_as_6355_, v_i_boxed_6365_, v_stop_boxed_6366_, v_b_6358_, v___y_6359_, v___y_6360_);
    crate::leanh::lean_dec(v___y_6360_);
    crate::leanh::lean_dec_ref(v___y_6359_);
    crate::leanh::lean_dec_ref(v_as_6355_);
    return v_res_6367_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(
    mut v_useErrorFormat_6370_: u8,
    mut v_groupByFilename_6371_: u8,
    mut v_verbose_6372_: u8,
    mut v_as_6373_: *mut crate::leanh::LeanObject,
    mut v_start_6374_: *mut crate::leanh::LeanObject,
    mut v_stop_6375_: *mut crate::leanh::LeanObject,
    mut v___y_6376_: *mut crate::leanh::LeanObject,
    mut v___y_6377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: u8 = 0;
    v___x_6379_ =
        l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0;
    v___x_6380_ = lean_nat_dec_lt(v_start_6374_, v_stop_6375_);
    if v___x_6380_ == 0 {
        let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6381_, 0, v___x_6379_);
        return v___x_6381_;
    } else {
        let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6383_: u8 = 0;
        v___x_6382_ = lean_array_get_size(v_as_6373_);
        v___x_6383_ = lean_nat_dec_le(v_stop_6375_, v___x_6382_);
        if v___x_6383_ == 0 {
            let mut v___x_6384_: u8 = 0;
            v___x_6384_ = lean_nat_dec_lt(v_start_6374_, v___x_6382_);
            if v___x_6384_ == 0 {
                let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6385_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6385_, 0, v___x_6379_);
                return v___x_6385_;
            } else {
                let mut v___x_6386_: usize = 0;
                let mut v___x_6387_: usize = 0;
                let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6386_ = lean_usize_of_nat(v_start_6374_);
                v___x_6387_ = lean_usize_of_nat(v___x_6382_);
                v___x_6388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_6370_, v_groupByFilename_6371_, v_verbose_6372_, v_as_6373_, v___x_6386_, v___x_6387_, v___x_6379_, v___y_6376_, v___y_6377_);
                return v___x_6388_;
            }
        } else {
            let mut v___x_6389_: usize = 0;
            let mut v___x_6390_: usize = 0;
            let mut v___x_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6389_ = lean_usize_of_nat(v_start_6374_);
            v___x_6390_ = lean_usize_of_nat(v_stop_6375_);
            v___x_6391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_6370_, v_groupByFilename_6371_, v_verbose_6372_, v_as_6373_, v___x_6389_, v___x_6390_, v___x_6379_, v___y_6376_, v___y_6377_);
            return v___x_6391_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(
    mut v_useErrorFormat_6392_: *mut crate::leanh::LeanObject,
    mut v_groupByFilename_6393_: *mut crate::leanh::LeanObject,
    mut v_verbose_6394_: *mut crate::leanh::LeanObject,
    mut v_as_6395_: *mut crate::leanh::LeanObject,
    mut v_start_6396_: *mut crate::leanh::LeanObject,
    mut v_stop_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useErrorFormat_boxed_6401_: u8 = 0;
    let mut v_groupByFilename_boxed_6402_: u8 = 0;
    let mut v_verbose_boxed_6403_: u8 = 0;
    let mut v_res_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useErrorFormat_boxed_6401_ = (crate::leanh::lean_unbox(v_useErrorFormat_6392_) as u8);
    v_groupByFilename_boxed_6402_ = (crate::leanh::lean_unbox(v_groupByFilename_6393_) as u8);
    v_verbose_boxed_6403_ = (crate::leanh::lean_unbox(v_verbose_6394_) as u8);
    v_res_6404_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(
        v_useErrorFormat_boxed_6401_,
        v_groupByFilename_boxed_6402_,
        v_verbose_boxed_6403_,
        v_as_6395_,
        v_start_6396_,
        v_stop_6397_,
        v___y_6398_,
        v___y_6399_,
    );
    crate::leanh::lean_dec(v___y_6399_);
    crate::leanh::lean_dec_ref(v___y_6398_);
    crate::leanh::lean_dec(v_stop_6397_);
    crate::leanh::lean_dec(v_start_6396_);
    crate::leanh::lean_dec_ref(v_as_6395_);
    return v_res_6404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(
    mut v_as_6405_: *mut crate::leanh::LeanObject,
    mut v_i_6406_: usize,
    mut v_stop_6407_: usize,
    mut v_b_6408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6409_: u8 = 0;
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: usize = 0;
    let mut v___x_6413_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6409_ = lean_usize_dec_eq(v_i_6406_, v_stop_6407_);
                if v___x_6409_ == 0 {
                    v___x_6410_ = lean_array_uget_borrowed(v_as_6405_, v_i_6406_);
                    v___x_6411_ = lean_nat_add(v_b_6408_, v___x_6410_);
                    crate::leanh::lean_dec(v_b_6408_);
                    v___x_6412_ = 1usize;
                    v___x_6413_ = lean_usize_add(v_i_6406_, v___x_6412_);
                    v_i_6406_ = v___x_6413_;
                    v_b_6408_ = v___x_6411_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6408_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(
    mut v_as_6415_: *mut crate::leanh::LeanObject,
    mut v_i_6416_: *mut crate::leanh::LeanObject,
    mut v_stop_6417_: *mut crate::leanh::LeanObject,
    mut v_b_6418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6419_: usize = 0;
    let mut v_stop_boxed_6420_: usize = 0;
    let mut v_res_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6419_ = crate::leanh::lean_unbox_usize(v_i_6416_);
    crate::leanh::lean_dec(v_i_6416_);
    v_stop_boxed_6420_ = crate::leanh::lean_unbox_usize(v_stop_6417_);
    crate::leanh::lean_dec(v_stop_6417_);
    v_res_6421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v_as_6415_, v_i_boxed_6419_, v_stop_boxed_6420_, v_b_6418_);
    crate::leanh::lean_dec_ref(v_as_6415_);
    return v_res_6421_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(
    mut v_as_6422_: *mut crate::leanh::LeanObject,
    mut v_i_6423_: usize,
    mut v_stop_6424_: usize,
    mut v_b_6425_: *mut crate::leanh::LeanObject,
    mut v___y_6426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6428_: u8 = 0;
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: usize = 0;
    let mut v___x_6435_: usize = 0;
    let mut v___x_6437_: u8 = 0;
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6442_: u8 = 0;
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6446_: u8 = 0;
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6428_ = lean_usize_dec_eq(v_i_6423_, v_stop_6424_);
                if v___x_6428_ == 0 {
                    v___x_6429_ = lean_array_uget_borrowed(v_as_6422_, v_i_6423_);
                    crate::leanh::lean_inc(v___x_6429_);
                    v___x_6430_ =
                        l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v___x_6429_, v___y_6426_);
                    if crate::leanh::lean_obj_tag(v___x_6430_) == 0 {
                        v_a_6431_ = crate::leanh::lean_ctor_get(v___x_6430_, 0);
                        crate::leanh::lean_inc(v_a_6431_);
                        crate::leanh::lean_dec_ref_known(v___x_6430_, 1);
                        v___x_6437_ = (crate::leanh::lean_unbox(v_a_6431_) as u8);
                        crate::leanh::lean_dec(v_a_6431_);
                        if v___x_6437_ == 0 {
                            v_a_6433_ = v_b_6425_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_6429_);
                            v___x_6438_ = lean_array_push(v_b_6425_, v___x_6429_);
                            v_a_6433_ = v___x_6438_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_6425_);
                        v_a_6439_ = crate::leanh::lean_ctor_get(v___x_6430_, 0);
                        v_isSharedCheck_6446_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6430_)) as u8;
                        if v_isSharedCheck_6446_ == 0 {
                            v___x_6441_ = v___x_6430_;
                            v_isShared_6442_ = v_isSharedCheck_6446_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6439_);
                            crate::leanh::lean_dec(v___x_6430_);
                            v___x_6441_ = crate::leanh::lean_box(0);
                            v_isShared_6442_ = v_isSharedCheck_6446_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_6447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6447_, 0, v_b_6425_);
                    return v___x_6447_;
                }
            }
            1 => {
                v___x_6434_ = 1usize;
                v___x_6435_ = lean_usize_add(v_i_6423_, v___x_6434_);
                v_i_6423_ = v___x_6435_;
                v_b_6425_ = v_a_6433_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6442_ == 0 {
                    v___x_6444_ = v___x_6441_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_a_6439_);
                    v___x_6444_ = v_reuseFailAlloc_6445_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(
    mut v_as_6448_: *mut crate::leanh::LeanObject,
    mut v_i_6449_: *mut crate::leanh::LeanObject,
    mut v_stop_6450_: *mut crate::leanh::LeanObject,
    mut v_b_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6454_: usize = 0;
    let mut v_stop_boxed_6455_: usize = 0;
    let mut v_res_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6454_ = crate::leanh::lean_unbox_usize(v_i_6449_);
    crate::leanh::lean_dec(v_i_6449_);
    v_stop_boxed_6455_ = crate::leanh::lean_unbox_usize(v_stop_6450_);
    crate::leanh::lean_dec(v_stop_6450_);
    v_res_6456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_6448_, v_i_boxed_6454_, v_stop_boxed_6455_, v_b_6451_, v___y_6452_);
    crate::leanh::lean_dec(v___y_6452_);
    crate::leanh::lean_dec_ref(v_as_6448_);
    return v_res_6456_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6458_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__0;
    v___x_6459_ = l_Lean_stringToMessageData(v___x_6458_);
    return v___x_6459_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6461_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__2;
    v___x_6462_ = l_Lean_stringToMessageData(v___x_6461_);
    return v___x_6462_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6464_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__4;
    v___x_6465_ = l_Lean_stringToMessageData(v___x_6464_);
    return v___x_6465_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6467_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__6;
    v___x_6468_ = l_Lean_stringToMessageData(v___x_6467_);
    return v___x_6468_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6470_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__8;
    v___x_6471_ = l_Lean_stringToMessageData(v___x_6470_);
    return v___x_6471_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6473_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__10;
    v___x_6474_ = l_Lean_stringToMessageData(v___x_6473_);
    return v___x_6474_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6476_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__12;
    v___x_6477_ = l_Lean_stringToMessageData(v___x_6476_);
    return v___x_6477_;
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6479_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__14;
    v___x_6480_ = l_Lean_stringToMessageData(v___x_6479_);
    return v___x_6480_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_formatLinterResults(
    mut v_results_6482_: *mut crate::leanh::LeanObject,
    mut v_decls_6483_: *mut crate::leanh::LeanObject,
    mut v_groupByFilename_6484_: u8,
    mut v_whereDesc_6485_: *mut crate::leanh::LeanObject,
    mut v_scope_6486_: u8,
    mut v_verbose_6487_: u8,
    mut v_numLinters_6488_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_6489_: u8,
    mut v_a_6490_: *mut crate::leanh::LeanObject,
    mut v_a_6491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: u8 = 0;
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6556_: usize = 0;
    let mut v___x_6557_: usize = 0;
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: u8 = 0;
    let mut v___x_6561_: u8 = 0;
    let mut v___x_6562_: usize = 0;
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: usize = 0;
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6572_: u8 = 0;
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: u8 = 0;
    let mut v___x_6579_: u8 = 0;
    let mut v___x_6580_: usize = 0;
    let mut v___x_6581_: usize = 0;
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: usize = 0;
    let mut v___x_6584_: usize = 0;
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6589_: u8 = 0;
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6499_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6500_ = lean_array_get_size(v_results_6482_);
                v___x_6501_ =
                    l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(
                        v_useErrorFormat_6489_,
                        v_groupByFilename_6484_,
                        v_verbose_6487_,
                        v_results_6482_,
                        v___x_6499_,
                        v___x_6500_,
                        v_a_6490_,
                        v_a_6491_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6501_) == 0 {
                    v_a_6502_ = crate::leanh::lean_ctor_get(v___x_6501_, 0);
                    crate::leanh::lean_inc(v_a_6502_);
                    crate::leanh::lean_dec_ref_known(v___x_6501_, 1);
                    v___x_6503_ = lean_array_to_list(v_a_6502_);
                    v___x_6504_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_printWarnings___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_printWarnings___closed__0_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0,
                    );
                    v___x_6505_ = l_Lean_MessageData_joinSep(v___x_6503_, v___x_6504_);
                    v___x_6506_ = lean_array_get_size(v_decls_6483_);
                    v___x_6577_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1;
                    v___x_6578_ = lean_nat_dec_lt(v___x_6499_, v___x_6506_);
                    if v___x_6578_ == 0 {
                        v_a_6554_ = v___x_6577_;
                        state = 4;
                        continue;
                    } else {
                        v___x_6579_ = lean_nat_dec_le(v___x_6506_, v___x_6506_);
                        if v___x_6579_ == 0 {
                            if v___x_6578_ == 0 {
                                v_a_6554_ = v___x_6577_;
                                state = 4;
                                continue;
                            } else {
                                v___x_6580_ = 0usize;
                                v___x_6581_ = lean_usize_of_nat(v___x_6506_);
                                v___x_6582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_6483_, v___x_6580_, v___x_6581_, v___x_6577_, v_a_6491_);
                                v___y_6567_ = v___x_6582_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_6583_ = 0usize;
                            v___x_6584_ = lean_usize_of_nat(v___x_6506_);
                            v___x_6585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_6483_, v___x_6583_, v___x_6584_, v___x_6577_, v_a_6491_);
                            v___y_6567_ = v___x_6585_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_numLinters_6488_);
                    crate::leanh::lean_dec_ref(v_whereDesc_6485_);
                    crate::leanh::lean_dec_ref(v_results_6482_);
                    v_a_6586_ = crate::leanh::lean_ctor_get(v___x_6501_, 0);
                    v_isSharedCheck_6593_ = (!crate::leanh::lean_is_exclusive(v___x_6501_)) as u8;
                    if v_isSharedCheck_6593_ == 0 {
                        v___x_6588_ = v___x_6501_;
                        v_isShared_6589_ = v_isSharedCheck_6593_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6586_);
                        crate::leanh::lean_dec(v___x_6501_);
                        v___x_6588_ = crate::leanh::lean_box(0);
                        v_isShared_6589_ = v_isSharedCheck_6593_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if v_scope_6486_ == 0 {
                    v___x_6495_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_formatLinterResults___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1,
                    );
                    v___x_6496_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6496_, 0, v_s_6494_);
                    crate::leanh::lean_ctor_set(v___x_6496_, 1, v___x_6495_);
                    v___x_6497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6497_, 0, v___x_6496_);
                    return v___x_6497_;
                } else {
                    v___x_6498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6498_, 0, v_s_6494_);
                    return v___x_6498_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_6510_);
                v___x_6511_ = l_Lean_stringToMessageData(v___y_6510_);
                v___x_6512_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6512_, 0, v___y_6509_);
                crate::leanh::lean_ctor_set(v___x_6512_, 1, v___x_6511_);
                v___x_6513_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3,
                );
                v___x_6514_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6514_, 0, v___x_6512_);
                crate::leanh::lean_ctor_set(v___x_6514_, 1, v___x_6513_);
                v___x_6515_ = lean_nat_sub(v___x_6506_, v___y_6508_);
                v___x_6516_ = l_Nat_reprFast(v___x_6515_);
                v___x_6517_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6517_, 0, v___x_6516_);
                v___x_6518_ = l_Lean_MessageData_ofFormat(v___x_6517_);
                v___x_6519_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6519_, 0, v___x_6514_);
                crate::leanh::lean_ctor_set(v___x_6519_, 1, v___x_6518_);
                v___x_6520_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5,
                );
                v___x_6521_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6521_, 0, v___x_6519_);
                crate::leanh::lean_ctor_set(v___x_6521_, 1, v___x_6520_);
                v___x_6522_ = l_Nat_reprFast(v___y_6508_);
                v___x_6523_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6523_, 0, v___x_6522_);
                v___x_6524_ = l_Lean_MessageData_ofFormat(v___x_6523_);
                v___x_6525_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6525_, 0, v___x_6521_);
                crate::leanh::lean_ctor_set(v___x_6525_, 1, v___x_6524_);
                v___x_6526_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7,
                );
                v___x_6527_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6527_, 0, v___x_6525_);
                crate::leanh::lean_ctor_set(v___x_6527_, 1, v___x_6526_);
                v___x_6528_ = l_Lean_stringToMessageData(v_whereDesc_6485_);
                v___x_6529_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6529_, 0, v___x_6527_);
                crate::leanh::lean_ctor_set(v___x_6529_, 1, v___x_6528_);
                v___x_6530_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9,
                );
                v___x_6531_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6531_, 0, v___x_6529_);
                crate::leanh::lean_ctor_set(v___x_6531_, 1, v___x_6530_);
                v___x_6532_ = l_Nat_reprFast(v_numLinters_6488_);
                v___x_6533_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6533_, 0, v___x_6532_);
                v___x_6534_ = l_Lean_MessageData_ofFormat(v___x_6533_);
                v___x_6535_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6535_, 0, v___x_6531_);
                crate::leanh::lean_ctor_set(v___x_6535_, 1, v___x_6534_);
                v___x_6536_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once
                    ),
                    _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11,
                );
                v___x_6537_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6537_, 0, v___x_6535_);
                crate::leanh::lean_ctor_set(v___x_6537_, 1, v___x_6536_);
                v___x_6538_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6538_, 0, v___x_6537_);
                crate::leanh::lean_ctor_set(v___x_6538_, 1, v___x_6505_);
                v_s_6494_ = v___x_6538_;
                state = 1;
                continue;
            }
            3 => {
                if v_verbose_6487_ == 0 {
                    crate::leanh::lean_dec(v___y_6541_);
                    crate::leanh::lean_dec(v___y_6540_);
                    crate::leanh::lean_dec(v_numLinters_6488_);
                    crate::leanh::lean_dec_ref(v_whereDesc_6485_);
                    v_s_6494_ = v___x_6505_;
                    state = 1;
                    continue;
                } else {
                    v___x_6542_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_formatLinterResults___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13,
                    );
                    crate::leanh::lean_inc(v___y_6541_);
                    v___x_6543_ = l_Nat_reprFast(v___y_6541_);
                    v___x_6544_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6544_, 0, v___x_6543_);
                    v___x_6545_ = l_Lean_MessageData_ofFormat(v___x_6544_);
                    v___x_6546_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6546_, 0, v___x_6542_);
                    crate::leanh::lean_ctor_set(v___x_6546_, 1, v___x_6545_);
                    v___x_6547_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_formatLinterResults___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once
                        ),
                        _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15,
                    );
                    v___x_6548_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6548_, 0, v___x_6546_);
                    crate::leanh::lean_ctor_set(v___x_6548_, 1, v___x_6547_);
                    v___x_6549_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6550_ = lean_nat_dec_eq(v___y_6541_, v___x_6549_);
                    crate::leanh::lean_dec(v___y_6541_);
                    if v___x_6550_ == 0 {
                        v___x_6551_ = l_Lean_Linter_EnvLinter_formatLinterResults___closed__16;
                        v___y_6508_ = v___y_6540_;
                        v___y_6509_ = v___x_6548_;
                        v___y_6510_ = v___x_6551_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0;
                        v___y_6508_ = v___y_6540_;
                        v___y_6509_ = v___x_6548_;
                        v___y_6510_ = v___x_6552_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6555_ = lean_array_get_size(v_a_6554_);
                crate::leanh::lean_dec_ref(v_a_6554_);
                v_sz_6556_ = lean_array_size(v_results_6482_);
                v___x_6557_ = 0usize;
                v___x_6558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_6556_, v___x_6557_, v_results_6482_);
                v___x_6559_ = lean_array_get_size(v___x_6558_);
                v___x_6560_ = lean_nat_dec_lt(v___x_6499_, v___x_6559_);
                if v___x_6560_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_6558_);
                    v___y_6540_ = v___x_6555_;
                    v___y_6541_ = v___x_6499_;
                    state = 3;
                    continue;
                } else {
                    v___x_6561_ = lean_nat_dec_le(v___x_6559_, v___x_6559_);
                    if v___x_6561_ == 0 {
                        if v___x_6560_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6558_);
                            v___y_6540_ = v___x_6555_;
                            v___y_6541_ = v___x_6499_;
                            state = 3;
                            continue;
                        } else {
                            v___x_6562_ = lean_usize_of_nat(v___x_6559_);
                            v___x_6563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_6558_, v___x_6557_, v___x_6562_, v___x_6499_);
                            crate::leanh::lean_dec_ref(v___x_6558_);
                            v___y_6540_ = v___x_6555_;
                            v___y_6541_ = v___x_6563_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6564_ = lean_usize_of_nat(v___x_6559_);
                        v___x_6565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_6558_, v___x_6557_, v___x_6564_, v___x_6499_);
                        crate::leanh::lean_dec_ref(v___x_6558_);
                        v___y_6540_ = v___x_6555_;
                        v___y_6541_ = v___x_6565_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_6567_) == 0 {
                    v_a_6568_ = crate::leanh::lean_ctor_get(v___y_6567_, 0);
                    crate::leanh::lean_inc(v_a_6568_);
                    crate::leanh::lean_dec_ref_known(v___y_6567_, 1);
                    v_a_6554_ = v_a_6568_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_6505_);
                    crate::leanh::lean_dec(v_numLinters_6488_);
                    crate::leanh::lean_dec_ref(v_whereDesc_6485_);
                    crate::leanh::lean_dec_ref(v_results_6482_);
                    v_a_6569_ = crate::leanh::lean_ctor_get(v___y_6567_, 0);
                    v_isSharedCheck_6576_ = (!crate::leanh::lean_is_exclusive(v___y_6567_)) as u8;
                    if v_isSharedCheck_6576_ == 0 {
                        v___x_6571_ = v___y_6567_;
                        v_isShared_6572_ = v_isSharedCheck_6576_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6569_);
                        crate::leanh::lean_dec(v___y_6567_);
                        v___x_6571_ = crate::leanh::lean_box(0);
                        v_isShared_6572_ = v_isSharedCheck_6576_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_6572_ == 0 {
                    v___x_6574_ = v___x_6571_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_a_6569_);
                    v___x_6574_ = v_reuseFailAlloc_6575_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6574_;
            }
            8 => {
                if v_isShared_6589_ == 0 {
                    v___x_6591_ = v___x_6588_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6592_, 0, v_a_6586_);
                    v___x_6591_ = v_reuseFailAlloc_6592_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_formatLinterResults___boxed(
    mut v_results_6594_: *mut crate::leanh::LeanObject,
    mut v_decls_6595_: *mut crate::leanh::LeanObject,
    mut v_groupByFilename_6596_: *mut crate::leanh::LeanObject,
    mut v_whereDesc_6597_: *mut crate::leanh::LeanObject,
    mut v_scope_6598_: *mut crate::leanh::LeanObject,
    mut v_verbose_6599_: *mut crate::leanh::LeanObject,
    mut v_numLinters_6600_: *mut crate::leanh::LeanObject,
    mut v_useErrorFormat_6601_: *mut crate::leanh::LeanObject,
    mut v_a_6602_: *mut crate::leanh::LeanObject,
    mut v_a_6603_: *mut crate::leanh::LeanObject,
    mut v_a_6604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_groupByFilename_boxed_6605_: u8 = 0;
    let mut v_scope_boxed_6606_: u8 = 0;
    let mut v_verbose_boxed_6607_: u8 = 0;
    let mut v_useErrorFormat_boxed_6608_: u8 = 0;
    let mut v_res_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_groupByFilename_boxed_6605_ = (crate::leanh::lean_unbox(v_groupByFilename_6596_) as u8);
    v_scope_boxed_6606_ = (crate::leanh::lean_unbox(v_scope_6598_) as u8);
    v_verbose_boxed_6607_ = (crate::leanh::lean_unbox(v_verbose_6599_) as u8);
    v_useErrorFormat_boxed_6608_ = (crate::leanh::lean_unbox(v_useErrorFormat_6601_) as u8);
    v_res_6609_ = l_Lean_Linter_EnvLinter_formatLinterResults(
        v_results_6594_,
        v_decls_6595_,
        v_groupByFilename_boxed_6605_,
        v_whereDesc_6597_,
        v_scope_boxed_6606_,
        v_verbose_boxed_6607_,
        v_numLinters_6600_,
        v_useErrorFormat_boxed_6608_,
        v_a_6602_,
        v_a_6603_,
    );
    crate::leanh::lean_dec(v_a_6603_);
    crate::leanh::lean_dec_ref(v_a_6602_);
    crate::leanh::lean_dec_ref(v_decls_6595_);
    return v_res_6609_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(
    mut v_as_6610_: *mut crate::leanh::LeanObject,
    mut v_i_6611_: usize,
    mut v_stop_6612_: usize,
    mut v_b_6613_: *mut crate::leanh::LeanObject,
    mut v___y_6614_: *mut crate::leanh::LeanObject,
    mut v___y_6615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_6610_, v_i_6611_, v_stop_6612_, v_b_6613_, v___y_6615_);
    return v___x_6617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(
    mut v_as_6618_: *mut crate::leanh::LeanObject,
    mut v_i_6619_: *mut crate::leanh::LeanObject,
    mut v_stop_6620_: *mut crate::leanh::LeanObject,
    mut v_b_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
    mut v___y_6624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6625_: usize = 0;
    let mut v_stop_boxed_6626_: usize = 0;
    let mut v_res_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6625_ = crate::leanh::lean_unbox_usize(v_i_6619_);
    crate::leanh::lean_dec(v_i_6619_);
    v_stop_boxed_6626_ = crate::leanh::lean_unbox_usize(v_stop_6620_);
    crate::leanh::lean_dec(v_stop_6620_);
    v_res_6627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(v_as_6618_, v_i_boxed_6625_, v_stop_boxed_6626_, v_b_6621_, v___y_6622_, v___y_6623_);
    crate::leanh::lean_dec(v___y_6623_);
    crate::leanh::lean_dec_ref(v___y_6622_);
    crate::leanh::lean_dec_ref(v_as_6618_);
    return v_res_6627_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(
    mut v_r_6628_: *mut crate::leanh::LeanObject,
    mut v_k_6629_: *mut crate::leanh::LeanObject,
    mut v_x_6630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6631_ = lean_array_push(v_r_6628_, v_k_6629_);
    return v___x_6631_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(
    mut v_r_6632_: *mut crate::leanh::LeanObject,
    mut v_k_6633_: *mut crate::leanh::LeanObject,
    mut v_x_6634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6635_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(
        v_r_6632_, v_k_6633_, v_x_6634_,
    );
    crate::leanh::lean_dec_ref(v_x_6634_);
    return v_res_6635_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(
    mut v_f_6636_: *mut crate::leanh::LeanObject,
    mut v_x1_6637_: *mut crate::leanh::LeanObject,
    mut v_x2_6638_: *mut crate::leanh::LeanObject,
    mut v_x3_6639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6640_ = crate::leanh::lean_apply_3(v_f_6636_, v_x1_6637_, v_x2_6638_, v_x3_6639_);
    return v___x_6640_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_f_6641_: *mut crate::leanh::LeanObject,
    mut v_keys_6642_: *mut crate::leanh::LeanObject,
    mut v_vals_6643_: *mut crate::leanh::LeanObject,
    mut v_i_6644_: *mut crate::leanh::LeanObject,
    mut v_acc_6645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: u8 = 0;
    let mut v_k_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6646_ = lean_array_get_size(v_keys_6642_);
                v___x_6647_ = lean_nat_dec_lt(v_i_6644_, v___x_6646_);
                if v___x_6647_ == 0 {
                    crate::leanh::lean_dec(v_i_6644_);
                    crate::leanh::lean_dec(v_f_6641_);
                    return v_acc_6645_;
                } else {
                    v_k_6648_ = lean_array_fget_borrowed(v_keys_6642_, v_i_6644_);
                    v_v_6649_ = lean_array_fget_borrowed(v_vals_6643_, v_i_6644_);
                    crate::leanh::lean_inc(v_f_6641_);
                    crate::leanh::lean_inc(v_v_6649_);
                    crate::leanh::lean_inc(v_k_6648_);
                    v___x_6650_ =
                        crate::leanh::lean_apply_3(v_f_6641_, v_acc_6645_, v_k_6648_, v_v_6649_);
                    v___x_6651_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6652_ = lean_nat_add(v_i_6644_, v___x_6651_);
                    crate::leanh::lean_dec(v_i_6644_);
                    v_i_6644_ = v___x_6652_;
                    v_acc_6645_ = v___x_6650_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_f_6654_: *mut crate::leanh::LeanObject,
    mut v_keys_6655_: *mut crate::leanh::LeanObject,
    mut v_vals_6656_: *mut crate::leanh::LeanObject,
    mut v_i_6657_: *mut crate::leanh::LeanObject,
    mut v_acc_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_6654_, v_keys_6655_, v_vals_6656_, v_i_6657_, v_acc_6658_);
    crate::leanh::lean_dec_ref(v_vals_6656_);
    crate::leanh::lean_dec_ref(v_keys_6655_);
    return v_res_6659_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(
    mut v_f_6660_: *mut crate::leanh::LeanObject,
    mut v_x_6661_: *mut crate::leanh::LeanObject,
    mut v_x_6662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6661_) == 0 {
        let mut v_es_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6666_: u8 = 0;
        v_es_6663_ = crate::leanh::lean_ctor_get(v_x_6661_, 0);
        v___x_6664_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_6665_ = lean_array_get_size(v_es_6663_);
        v___x_6666_ = lean_nat_dec_lt(v___x_6664_, v___x_6665_);
        if v___x_6666_ == 0 {
            crate::leanh::lean_dec(v_f_6660_);
            return v_x_6662_;
        } else {
            let mut v___x_6667_: u8 = 0;
            v___x_6667_ = lean_nat_dec_le(v___x_6665_, v___x_6665_);
            if v___x_6667_ == 0 {
                if v___x_6666_ == 0 {
                    crate::leanh::lean_dec(v_f_6660_);
                    return v_x_6662_;
                } else {
                    let mut v___x_6668_: usize = 0;
                    let mut v___x_6669_: usize = 0;
                    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_6668_ = 0usize;
                    v___x_6669_ = lean_usize_of_nat(v___x_6665_);
                    v___x_6670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_6660_, v_es_6663_, v___x_6668_, v___x_6669_, v_x_6662_);
                    return v___x_6670_;
                }
            } else {
                let mut v___x_6671_: usize = 0;
                let mut v___x_6672_: usize = 0;
                let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6671_ = 0usize;
                v___x_6672_ = lean_usize_of_nat(v___x_6665_);
                v___x_6673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_6660_, v_es_6663_, v___x_6671_, v___x_6672_, v_x_6662_);
                return v___x_6673_;
            }
        }
    } else {
        let mut v_ks_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_6674_ = crate::leanh::lean_ctor_get(v_x_6661_, 0);
        v_vs_6675_ = crate::leanh::lean_ctor_get(v_x_6661_, 1);
        v___x_6676_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_6677_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_6660_, v_ks_6674_, v_vs_6675_, v___x_6676_, v_x_6662_);
        return v___x_6677_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_f_6678_: *mut crate::leanh::LeanObject,
    mut v_as_6679_: *mut crate::leanh::LeanObject,
    mut v_i_6680_: usize,
    mut v_stop_6681_: usize,
    mut v_b_6682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: usize = 0;
    let mut v___x_6686_: usize = 0;
    let mut v___x_6688_: u8 = 0;
    let mut v___x_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6688_ = lean_usize_dec_eq(v_i_6680_, v_stop_6681_);
                if v___x_6688_ == 0 {
                    v___x_6689_ = lean_array_uget_borrowed(v_as_6679_, v_i_6680_);
                    match crate::leanh::lean_obj_tag(v___x_6689_) {
                        0 => {
                            v_key_6690_ = crate::leanh::lean_ctor_get(v___x_6689_, 0);
                            v_val_6691_ = crate::leanh::lean_ctor_get(v___x_6689_, 1);
                            crate::leanh::lean_inc(v_f_6678_);
                            crate::leanh::lean_inc(v_val_6691_);
                            crate::leanh::lean_inc(v_key_6690_);
                            v___x_6692_ = crate::leanh::lean_apply_3(
                                v_f_6678_,
                                v_b_6682_,
                                v_key_6690_,
                                v_val_6691_,
                            );
                            v___y_6684_ = v___x_6692_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_6693_ = crate::leanh::lean_ctor_get(v___x_6689_, 0);
                            crate::leanh::lean_inc(v_f_6678_);
                            v___x_6694_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_6678_, v_node_6693_, v_b_6682_);
                            v___y_6684_ = v___x_6694_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_6684_ = v_b_6682_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_6678_);
                    return v_b_6682_;
                }
            }
            1 => {
                v___x_6685_ = 1usize;
                v___x_6686_ = lean_usize_add(v_i_6680_, v___x_6685_);
                v_i_6680_ = v___x_6686_;
                v_b_6682_ = v___y_6684_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_f_6695_: *mut crate::leanh::LeanObject,
    mut v_as_6696_: *mut crate::leanh::LeanObject,
    mut v_i_6697_: *mut crate::leanh::LeanObject,
    mut v_stop_6698_: *mut crate::leanh::LeanObject,
    mut v_b_6699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6700_: usize = 0;
    let mut v_stop_boxed_6701_: usize = 0;
    let mut v_res_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6700_ = crate::leanh::lean_unbox_usize(v_i_6697_);
    crate::leanh::lean_dec(v_i_6697_);
    v_stop_boxed_6701_ = crate::leanh::lean_unbox_usize(v_stop_6698_);
    crate::leanh::lean_dec(v_stop_6698_);
    v_res_6702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_6695_, v_as_6696_, v_i_boxed_6700_, v_stop_boxed_6701_, v_b_6699_);
    crate::leanh::lean_dec_ref(v_as_6696_);
    return v_res_6702_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_6703_: *mut crate::leanh::LeanObject,
    mut v_x_6704_: *mut crate::leanh::LeanObject,
    mut v_x_6705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6706_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_6703_, v_x_6704_, v_x_6705_);
    crate::leanh::lean_dec_ref(v_x_6704_);
    return v_res_6706_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(
    mut v_map_6707_: *mut crate::leanh::LeanObject,
    mut v_f_6708_: *mut crate::leanh::LeanObject,
    mut v_init_6709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6710_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_6710_, 0, v_f_6708_);
    v___x_6711_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v___f_6710_, v_map_6707_, v_init_6709_);
    return v___x_6711_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(
    mut v_map_6712_: *mut crate::leanh::LeanObject,
    mut v_f_6713_: *mut crate::leanh::LeanObject,
    mut v_init_6714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6715_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_6712_, v_f_6713_, v_init_6714_);
    crate::leanh::lean_dec_ref(v_map_6712_);
    return v_res_6715_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(
    mut v_a_6717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6719_ = lean_st_ref_get(v_a_6717_);
    v_env_6720_ = crate::leanh::lean_ctor_get(v___x_6719_, 0);
    crate::leanh::lean_inc_ref(v_env_6720_);
    crate::leanh::lean_dec(v___x_6719_);
    v___x_6721_ = l_Lean_Environment_constants(v_env_6720_);
    v_map_u2082_6722_ = crate::leanh::lean_ctor_get(v___x_6721_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_6722_);
    crate::leanh::lean_dec_ref(v___x_6721_);
    v___f_6723_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0;
    v___x_6724_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1;
    v___x_6725_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_u2082_6722_, v___f_6723_, v___x_6724_);
    crate::leanh::lean_dec_ref(v_map_u2082_6722_);
    v___x_6726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6726_, 0, v___x_6725_);
    return v___x_6726_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(
    mut v_a_6727_: *mut crate::leanh::LeanObject,
    mut v_a_6728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6729_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_6727_);
    crate::leanh::lean_dec(v_a_6727_);
    return v_res_6729_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInCurrModule(
    mut v_a_6730_: *mut crate::leanh::LeanObject,
    mut v_a_6731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6733_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_6731_);
    return v___x_6733_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(
    mut v_a_6734_: *mut crate::leanh::LeanObject,
    mut v_a_6735_: *mut crate::leanh::LeanObject,
    mut v_a_6736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6737_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule(v_a_6734_, v_a_6735_);
    crate::leanh::lean_dec(v_a_6735_);
    crate::leanh::lean_dec_ref(v_a_6734_);
    return v_res_6737_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(
    mut v_00_u03c3_6738_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6739_: *mut crate::leanh::LeanObject,
    mut v_map_6740_: *mut crate::leanh::LeanObject,
    mut v_f_6741_: *mut crate::leanh::LeanObject,
    mut v_init_6742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6743_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_6740_, v_f_6741_, v_init_6742_);
    return v___x_6743_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(
    mut v_00_u03c3_6744_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6745_: *mut crate::leanh::LeanObject,
    mut v_map_6746_: *mut crate::leanh::LeanObject,
    mut v_f_6747_: *mut crate::leanh::LeanObject,
    mut v_init_6748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6749_ =
        l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(
            v_00_u03c3_6744_,
            v_00_u03b2_6745_,
            v_map_6746_,
            v_f_6747_,
            v_init_6748_,
        );
    crate::leanh::lean_dec_ref(v_map_6746_);
    return v_res_6749_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(
    mut v_map_6750_: *mut crate::leanh::LeanObject,
    mut v_f_6751_: *mut crate::leanh::LeanObject,
    mut v_init_6752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6753_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_6751_, v_map_6750_, v_init_6752_);
    return v___x_6753_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(
    mut v_map_6754_: *mut crate::leanh::LeanObject,
    mut v_f_6755_: *mut crate::leanh::LeanObject,
    mut v_init_6756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6757_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(v_map_6754_, v_f_6755_, v_init_6756_);
    crate::leanh::lean_dec_ref(v_map_6754_);
    return v_res_6757_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(
    mut v_00_u03c3_6758_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6759_: *mut crate::leanh::LeanObject,
    mut v_map_6760_: *mut crate::leanh::LeanObject,
    mut v_f_6761_: *mut crate::leanh::LeanObject,
    mut v_init_6762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6763_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_6761_, v_map_6760_, v_init_6762_);
    return v___x_6763_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(
    mut v_00_u03c3_6764_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6765_: *mut crate::leanh::LeanObject,
    mut v_map_6766_: *mut crate::leanh::LeanObject,
    mut v_f_6767_: *mut crate::leanh::LeanObject,
    mut v_init_6768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6769_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(v_00_u03c3_6764_, v_00_u03b2_6765_, v_map_6766_, v_f_6767_, v_init_6768_);
    crate::leanh::lean_dec_ref(v_map_6766_);
    return v_res_6769_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(
    mut v_00_u03c3_6770_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6771_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6772_: *mut crate::leanh::LeanObject,
    mut v_f_6773_: *mut crate::leanh::LeanObject,
    mut v_x_6774_: *mut crate::leanh::LeanObject,
    mut v_x_6775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6776_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_6773_, v_x_6774_, v_x_6775_);
    return v___x_6776_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_6777_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6778_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6779_: *mut crate::leanh::LeanObject,
    mut v_f_6780_: *mut crate::leanh::LeanObject,
    mut v_x_6781_: *mut crate::leanh::LeanObject,
    mut v_x_6782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6783_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(v_00_u03c3_6777_, v_00_u03b1_6778_, v_00_u03b2_6779_, v_f_6780_, v_x_6781_, v_x_6782_);
    crate::leanh::lean_dec_ref(v_x_6781_);
    return v_res_6783_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_6784_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6785_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6786_: *mut crate::leanh::LeanObject,
    mut v_f_6787_: *mut crate::leanh::LeanObject,
    mut v_as_6788_: *mut crate::leanh::LeanObject,
    mut v_i_6789_: usize,
    mut v_stop_6790_: usize,
    mut v_b_6791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_6787_, v_as_6788_, v_i_6789_, v_stop_6790_, v_b_6791_);
    return v___x_6792_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_6793_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6794_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6795_: *mut crate::leanh::LeanObject,
    mut v_f_6796_: *mut crate::leanh::LeanObject,
    mut v_as_6797_: *mut crate::leanh::LeanObject,
    mut v_i_6798_: *mut crate::leanh::LeanObject,
    mut v_stop_6799_: *mut crate::leanh::LeanObject,
    mut v_b_6800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6801_: usize = 0;
    let mut v_stop_boxed_6802_: usize = 0;
    let mut v_res_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6801_ = crate::leanh::lean_unbox_usize(v_i_6798_);
    crate::leanh::lean_dec(v_i_6798_);
    v_stop_boxed_6802_ = crate::leanh::lean_unbox_usize(v_stop_6799_);
    crate::leanh::lean_dec(v_stop_6799_);
    v_res_6803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_6793_, v_00_u03b2_6794_, v_00_u03c3_6795_, v_f_6796_, v_as_6797_, v_i_boxed_6801_, v_stop_boxed_6802_, v_b_6800_);
    crate::leanh::lean_dec_ref(v_as_6797_);
    return v_res_6803_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03c3_6804_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6806_: *mut crate::leanh::LeanObject,
    mut v_f_6807_: *mut crate::leanh::LeanObject,
    mut v_keys_6808_: *mut crate::leanh::LeanObject,
    mut v_vals_6809_: *mut crate::leanh::LeanObject,
    mut v_heq_6810_: *mut crate::leanh::LeanObject,
    mut v_i_6811_: *mut crate::leanh::LeanObject,
    mut v_acc_6812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6813_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_6807_, v_keys_6808_, v_vals_6809_, v_i_6811_, v_acc_6812_);
    return v___x_6813_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03c3_6814_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6815_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6816_: *mut crate::leanh::LeanObject,
    mut v_f_6817_: *mut crate::leanh::LeanObject,
    mut v_keys_6818_: *mut crate::leanh::LeanObject,
    mut v_vals_6819_: *mut crate::leanh::LeanObject,
    mut v_heq_6820_: *mut crate::leanh::LeanObject,
    mut v_i_6821_: *mut crate::leanh::LeanObject,
    mut v_acc_6822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_6814_, v_00_u03b1_6815_, v_00_u03b2_6816_, v_f_6817_, v_keys_6818_, v_vals_6819_, v_heq_6820_, v_i_6821_, v_acc_6822_);
    crate::leanh::lean_dec_ref(v_vals_6819_);
    crate::leanh::lean_dec_ref(v_keys_6818_);
    return v_res_6823_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(
    mut v_x_6824_: *mut crate::leanh::LeanObject,
    mut v_x_6825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6825_) == 0 {
                    return v_x_6824_;
                } else {
                    v_key_6826_ = crate::leanh::lean_ctor_get(v_x_6825_, 0);
                    crate::leanh::lean_inc(v_key_6826_);
                    v_tail_6827_ = crate::leanh::lean_ctor_get(v_x_6825_, 2);
                    crate::leanh::lean_inc(v_tail_6827_);
                    crate::leanh::lean_dec_ref_known(v_x_6825_, 3);
                    v___x_6828_ = lean_array_push(v_x_6824_, v_key_6826_);
                    v_x_6824_ = v___x_6828_;
                    v_x_6825_ = v_tail_6827_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(
    mut v_as_6830_: *mut crate::leanh::LeanObject,
    mut v_i_6831_: usize,
    mut v_stop_6832_: usize,
    mut v_b_6833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6834_: u8 = 0;
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: usize = 0;
    let mut v___x_6838_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6834_ = lean_usize_dec_eq(v_i_6831_, v_stop_6832_);
                if v___x_6834_ == 0 {
                    v___x_6835_ = lean_array_uget_borrowed(v_as_6830_, v_i_6831_);
                    crate::leanh::lean_inc(v___x_6835_);
                    v___x_6836_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(v_b_6833_, v___x_6835_);
                    v___x_6837_ = 1usize;
                    v___x_6838_ = lean_usize_add(v_i_6831_, v___x_6837_);
                    v_i_6831_ = v___x_6838_;
                    v_b_6833_ = v___x_6836_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6833_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(
    mut v_as_6840_: *mut crate::leanh::LeanObject,
    mut v_i_6841_: *mut crate::leanh::LeanObject,
    mut v_stop_6842_: *mut crate::leanh::LeanObject,
    mut v_b_6843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6844_: usize = 0;
    let mut v_stop_boxed_6845_: usize = 0;
    let mut v_res_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6844_ = crate::leanh::lean_unbox_usize(v_i_6841_);
    crate::leanh::lean_dec(v_i_6841_);
    v_stop_boxed_6845_ = crate::leanh::lean_unbox_usize(v_stop_6842_);
    crate::leanh::lean_dec(v_stop_6842_);
    v_res_6846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_as_6840_, v_i_boxed_6844_, v_stop_boxed_6845_, v_b_6843_);
    crate::leanh::lean_dec_ref(v_as_6840_);
    return v_res_6846_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getAllDecls___redArg(
    mut v_a_6847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2081_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: u8 = 0;
    let mut v___x_6859_: u8 = 0;
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6862_: u8 = 0;
    let mut v___x_6863_: usize = 0;
    let mut v___x_6864_: usize = 0;
    let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6869_: u8 = 0;
    let mut v_unused_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6873_: u8 = 0;
    let mut v___x_6874_: usize = 0;
    let mut v___x_6875_: usize = 0;
    let mut v___x_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6880_: u8 = 0;
    let mut v_unused_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6849_ = lean_st_ref_get(v_a_6847_);
                v___x_6850_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_6847_);
                v_a_6851_ = crate::leanh::lean_ctor_get(v___x_6850_, 0);
                crate::leanh::lean_inc(v_a_6851_);
                v_env_6852_ = crate::leanh::lean_ctor_get(v___x_6849_, 0);
                crate::leanh::lean_inc_ref(v_env_6852_);
                crate::leanh::lean_dec(v___x_6849_);
                v___x_6853_ = l_Lean_Environment_constants(v_env_6852_);
                v_map_u2081_6854_ = crate::leanh::lean_ctor_get(v___x_6853_, 0);
                crate::leanh::lean_inc_ref(v_map_u2081_6854_);
                crate::leanh::lean_dec_ref(v___x_6853_);
                v_buckets_6855_ = crate::leanh::lean_ctor_get(v_map_u2081_6854_, 1);
                crate::leanh::lean_inc_ref(v_buckets_6855_);
                crate::leanh::lean_dec_ref(v_map_u2081_6854_);
                v___x_6856_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6857_ = lean_array_get_size(v_buckets_6855_);
                v___x_6858_ = lean_nat_dec_lt(v___x_6856_, v___x_6857_);
                if v___x_6858_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_6855_);
                    crate::leanh::lean_dec(v_a_6851_);
                    return v___x_6850_;
                } else {
                    v___x_6859_ = lean_nat_dec_le(v___x_6857_, v___x_6857_);
                    if v___x_6859_ == 0 {
                        if v___x_6858_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_6855_);
                            crate::leanh::lean_dec(v_a_6851_);
                            return v___x_6850_;
                        } else {
                            v_isSharedCheck_6869_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6850_)) as u8;
                            if v_isSharedCheck_6869_ == 0 {
                                v_unused_6870_ = crate::leanh::lean_ctor_get(v___x_6850_, 0);
                                crate::leanh::lean_dec(v_unused_6870_);
                                v___x_6861_ = v___x_6850_;
                                v_isShared_6862_ = v_isSharedCheck_6869_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6850_);
                                v___x_6861_ = crate::leanh::lean_box(0);
                                v_isShared_6862_ = v_isSharedCheck_6869_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_isSharedCheck_6880_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6850_)) as u8;
                        if v_isSharedCheck_6880_ == 0 {
                            v_unused_6881_ = crate::leanh::lean_ctor_get(v___x_6850_, 0);
                            crate::leanh::lean_dec(v_unused_6881_);
                            v___x_6872_ = v___x_6850_;
                            v_isShared_6873_ = v_isSharedCheck_6880_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6850_);
                            v___x_6872_ = crate::leanh::lean_box(0);
                            v_isShared_6873_ = v_isSharedCheck_6880_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6863_ = 0usize;
                v___x_6864_ = lean_usize_of_nat(v___x_6857_);
                v___x_6865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_6855_, v___x_6863_, v___x_6864_, v_a_6851_);
                crate::leanh::lean_dec_ref(v_buckets_6855_);
                if v_isShared_6862_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6861_, 0, v___x_6865_);
                    v___x_6867_ = v___x_6861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6868_, 0, v___x_6865_);
                    v___x_6867_ = v_reuseFailAlloc_6868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6867_;
            }
            3 => {
                v___x_6874_ = 0usize;
                v___x_6875_ = lean_usize_of_nat(v___x_6857_);
                v___x_6876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_6855_, v___x_6874_, v___x_6875_, v_a_6851_);
                crate::leanh::lean_dec_ref(v_buckets_6855_);
                if v_isShared_6873_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6872_, 0, v___x_6876_);
                    v___x_6878_ = v___x_6872_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6879_, 0, v___x_6876_);
                    v___x_6878_ = v_reuseFailAlloc_6879_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(
    mut v_a_6882_: *mut crate::leanh::LeanObject,
    mut v_a_6883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6884_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_6882_);
    crate::leanh::lean_dec(v_a_6882_);
    return v_res_6884_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getAllDecls(
    mut v_a_6885_: *mut crate::leanh::LeanObject,
    mut v_a_6886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6888_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_6886_);
    return v___x_6888_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getAllDecls___boxed(
    mut v_a_6889_: *mut crate::leanh::LeanObject,
    mut v_a_6890_: *mut crate::leanh::LeanObject,
    mut v_a_6891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6892_ = l_Lean_Linter_EnvLinter_getAllDecls(v_a_6889_, v_a_6890_);
    crate::leanh::lean_dec(v_a_6890_);
    crate::leanh::lean_dec_ref(v_a_6889_);
    return v_res_6892_;
}
pub unsafe fn l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(
    mut v_msg_6893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6894_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6895_ = lean_panic_fn_borrowed(v___x_6894_, v_msg_6893_);
    return v___x_6895_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2;
    v___x_6900_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_6901_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_6902_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1;
    v___x_6903_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0;
    v___x_6904_ = l_mkPanicMessageWithDecl(
        v___x_6903_,
        v___x_6902_,
        v___x_6901_,
        v___x_6900_,
        v___x_6899_,
    );
    return v___x_6904_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(
    mut v___x_6905_: *mut crate::leanh::LeanObject,
    mut v___x_6906_: *mut crate::leanh::LeanObject,
    mut v_x_6907_: *mut crate::leanh::LeanObject,
    mut v_x_6908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: u8 = 0;
    let mut v___y_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: u8 = 0;
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6908_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_6906_);
                    return v_x_6907_;
                } else {
                    v_key_6909_ = crate::leanh::lean_ctor_get(v_x_6908_, 0);
                    crate::leanh::lean_inc(v_key_6909_);
                    v_tail_6910_ = crate::leanh::lean_ctor_get(v_x_6908_, 2);
                    crate::leanh::lean_inc(v_tail_6910_);
                    crate::leanh::lean_dec_ref_known(v_x_6908_, 3);
                    v___x_6911_ = 0;
                    crate::leanh::lean_inc_ref(v___x_6906_);
                    v___x_6920_ = l_Lean_Environment_const2ModIdx(v___x_6906_);
                    v___x_6921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v___x_6920_, v_key_6909_);
                    crate::leanh::lean_dec_ref(v___x_6920_);
                    if crate::leanh::lean_obj_tag(v___x_6921_) == 0 {
                        v___x_6922_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3);
                        v___x_6923_ =
                            l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(
                                v___x_6922_,
                            );
                        v___y_6913_ = v___x_6923_;
                        state = 1;
                        continue;
                    } else {
                        v_val_6924_ = crate::leanh::lean_ctor_get(v___x_6921_, 0);
                        crate::leanh::lean_inc(v_val_6924_);
                        crate::leanh::lean_dec_ref_known(v___x_6921_, 1);
                        v___y_6913_ = v_val_6924_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6914_ = crate::leanh::lean_box((v___x_6911_) as usize);
                v___x_6915_ = lean_array_get(v___x_6914_, v___x_6905_, v___y_6913_);
                crate::leanh::lean_dec(v___y_6913_);
                crate::leanh::lean_dec(v___x_6914_);
                v___x_6916_ = (crate::leanh::lean_unbox(v___x_6915_) as u8);
                crate::leanh::lean_dec(v___x_6915_);
                if v___x_6916_ == 0 {
                    crate::leanh::lean_dec(v_key_6909_);
                    v_x_6908_ = v_tail_6910_;
                    state = 0;
                    continue;
                } else {
                    v___x_6918_ = lean_array_push(v_x_6907_, v_key_6909_);
                    v_x_6907_ = v___x_6918_;
                    v_x_6908_ = v_tail_6910_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(
    mut v___x_6925_: *mut crate::leanh::LeanObject,
    mut v___x_6926_: *mut crate::leanh::LeanObject,
    mut v_x_6927_: *mut crate::leanh::LeanObject,
    mut v_x_6928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6929_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_6925_, v___x_6926_, v_x_6927_, v_x_6928_);
    crate::leanh::lean_dec_ref(v___x_6925_);
    return v_res_6929_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(
    mut v___x_6930_: *mut crate::leanh::LeanObject,
    mut v___x_6931_: *mut crate::leanh::LeanObject,
    mut v_as_6932_: *mut crate::leanh::LeanObject,
    mut v_i_6933_: usize,
    mut v_stop_6934_: usize,
    mut v_b_6935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6936_: u8 = 0;
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: usize = 0;
    let mut v___x_6940_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6936_ = lean_usize_dec_eq(v_i_6933_, v_stop_6934_);
                if v___x_6936_ == 0 {
                    v___x_6937_ = lean_array_uget_borrowed(v_as_6932_, v_i_6933_);
                    crate::leanh::lean_inc(v___x_6937_);
                    crate::leanh::lean_inc_ref(v___x_6931_);
                    v___x_6938_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_6930_, v___x_6931_, v_b_6935_, v___x_6937_);
                    v___x_6939_ = 1usize;
                    v___x_6940_ = lean_usize_add(v_i_6933_, v___x_6939_);
                    v_i_6933_ = v___x_6940_;
                    v_b_6935_ = v___x_6938_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_6931_);
                    return v_b_6935_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(
    mut v___x_6942_: *mut crate::leanh::LeanObject,
    mut v___x_6943_: *mut crate::leanh::LeanObject,
    mut v_as_6944_: *mut crate::leanh::LeanObject,
    mut v_i_6945_: *mut crate::leanh::LeanObject,
    mut v_stop_6946_: *mut crate::leanh::LeanObject,
    mut v_b_6947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6948_: usize = 0;
    let mut v_stop_boxed_6949_: usize = 0;
    let mut v_res_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6948_ = crate::leanh::lean_unbox_usize(v_i_6945_);
    crate::leanh::lean_dec(v_i_6945_);
    v_stop_boxed_6949_ = crate::leanh::lean_unbox_usize(v_stop_6946_);
    crate::leanh::lean_dec(v_stop_6946_);
    v_res_6950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_6942_, v___x_6943_, v_as_6944_, v_i_boxed_6948_, v_stop_boxed_6949_, v_b_6947_);
    crate::leanh::lean_dec_ref(v_as_6944_);
    crate::leanh::lean_dec_ref(v___x_6942_);
    return v_res_6950_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(
    mut v_pkg_6951_: *mut crate::leanh::LeanObject,
    mut v_sz_6952_: usize,
    mut v_i_6953_: usize,
    mut v_bs_6954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6955_: u8 = 0;
    let mut v_v_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: u8 = 0;
    let mut v___x_6960_: usize = 0;
    let mut v___x_6961_: usize = 0;
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6955_ = lean_usize_dec_lt(v_i_6953_, v_sz_6952_);
                if v___x_6955_ == 0 {
                    return v_bs_6954_;
                } else {
                    v_v_6956_ = lean_array_uget(v_bs_6954_, v_i_6953_);
                    v___x_6957_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6958_ = lean_array_uset(v_bs_6954_, v_i_6953_, v___x_6957_);
                    v___x_6959_ = l_Lean_Name_isPrefixOf(v_pkg_6951_, v_v_6956_);
                    crate::leanh::lean_dec(v_v_6956_);
                    v___x_6960_ = 1usize;
                    v___x_6961_ = lean_usize_add(v_i_6953_, v___x_6960_);
                    v___x_6962_ = crate::leanh::lean_box((v___x_6959_) as usize);
                    v___x_6963_ = lean_array_uset(v_bs_x27_6958_, v_i_6953_, v___x_6962_);
                    v_i_6953_ = v___x_6961_;
                    v_bs_6954_ = v___x_6963_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(
    mut v_pkg_6965_: *mut crate::leanh::LeanObject,
    mut v_sz_6966_: *mut crate::leanh::LeanObject,
    mut v_i_6967_: *mut crate::leanh::LeanObject,
    mut v_bs_6968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6969_: usize = 0;
    let mut v_i_boxed_6970_: usize = 0;
    let mut v_res_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6969_ = crate::leanh::lean_unbox_usize(v_sz_6966_);
    crate::leanh::lean_dec(v_sz_6966_);
    v_i_boxed_6970_ = crate::leanh::lean_unbox_usize(v_i_6967_);
    crate::leanh::lean_dec(v_i_6967_);
    v_res_6971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_6965_, v_sz_boxed_6969_, v_i_boxed_6970_, v_bs_6968_);
    crate::leanh::lean_dec(v_pkg_6965_);
    return v_res_6971_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(
    mut v_pkg_6972_: *mut crate::leanh::LeanObject,
    mut v_a_6973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2081_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: u8 = 0;
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6987_: usize = 0;
    let mut v___x_6988_: usize = 0;
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: u8 = 0;
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6993_: u8 = 0;
    let mut v___x_6994_: usize = 0;
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut v_unused_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7004_: usize = 0;
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7009_: u8 = 0;
    let mut v_unused_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6975_ = lean_st_ref_get(v_a_6973_);
                v___x_6976_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_6973_);
                v_a_6977_ = crate::leanh::lean_ctor_get(v___x_6976_, 0);
                crate::leanh::lean_inc(v_a_6977_);
                v_env_6978_ = crate::leanh::lean_ctor_get(v___x_6975_, 0);
                crate::leanh::lean_inc_ref_n(v_env_6978_, 2);
                crate::leanh::lean_dec(v___x_6975_);
                v___x_6979_ = l_Lean_Environment_header(v_env_6978_);
                v___x_6980_ = l_Lean_Environment_constants(v_env_6978_);
                v_map_u2081_6981_ = crate::leanh::lean_ctor_get(v___x_6980_, 0);
                crate::leanh::lean_inc_ref(v_map_u2081_6981_);
                crate::leanh::lean_dec_ref(v___x_6980_);
                v_buckets_6982_ = crate::leanh::lean_ctor_get(v_map_u2081_6981_, 1);
                crate::leanh::lean_inc_ref(v_buckets_6982_);
                crate::leanh::lean_dec_ref(v_map_u2081_6981_);
                v___x_6983_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6984_ = lean_array_get_size(v_buckets_6982_);
                v___x_6985_ = lean_nat_dec_lt(v___x_6983_, v___x_6984_);
                if v___x_6985_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_6982_);
                    crate::leanh::lean_dec_ref(v___x_6979_);
                    crate::leanh::lean_dec_ref(v_env_6978_);
                    crate::leanh::lean_dec(v_a_6977_);
                    return v___x_6976_;
                } else {
                    v___x_6986_ = l_Lean_EnvironmentHeader_moduleNames(v___x_6979_);
                    v_sz_6987_ = lean_array_size(v___x_6986_);
                    v___x_6988_ = 0usize;
                    v___x_6989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_6972_, v_sz_6987_, v___x_6988_, v___x_6986_);
                    v___x_6990_ = lean_nat_dec_le(v___x_6984_, v___x_6984_);
                    if v___x_6990_ == 0 {
                        if v___x_6985_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6989_);
                            crate::leanh::lean_dec_ref(v_buckets_6982_);
                            crate::leanh::lean_dec_ref(v_env_6978_);
                            crate::leanh::lean_dec(v_a_6977_);
                            return v___x_6976_;
                        } else {
                            v_isSharedCheck_6999_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6976_)) as u8;
                            if v_isSharedCheck_6999_ == 0 {
                                v_unused_7000_ = crate::leanh::lean_ctor_get(v___x_6976_, 0);
                                crate::leanh::lean_dec(v_unused_7000_);
                                v___x_6992_ = v___x_6976_;
                                v_isShared_6993_ = v_isSharedCheck_6999_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6976_);
                                v___x_6992_ = crate::leanh::lean_box(0);
                                v_isShared_6993_ = v_isSharedCheck_6999_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_isSharedCheck_7009_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6976_)) as u8;
                        if v_isSharedCheck_7009_ == 0 {
                            v_unused_7010_ = crate::leanh::lean_ctor_get(v___x_6976_, 0);
                            crate::leanh::lean_dec(v_unused_7010_);
                            v___x_7002_ = v___x_6976_;
                            v_isShared_7003_ = v_isSharedCheck_7009_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6976_);
                            v___x_7002_ = crate::leanh::lean_box(0);
                            v_isShared_7003_ = v_isSharedCheck_7009_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6994_ = lean_usize_of_nat(v___x_6984_);
                v___x_6995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_6989_, v_env_6978_, v_buckets_6982_, v___x_6988_, v___x_6994_, v_a_6977_);
                crate::leanh::lean_dec_ref(v_buckets_6982_);
                crate::leanh::lean_dec_ref(v___x_6989_);
                if v_isShared_6993_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6992_, 0, v___x_6995_);
                    v___x_6997_ = v___x_6992_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6998_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6998_, 0, v___x_6995_);
                    v___x_6997_ = v_reuseFailAlloc_6998_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6997_;
            }
            3 => {
                v___x_7004_ = lean_usize_of_nat(v___x_6984_);
                v___x_7005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_6989_, v_env_6978_, v_buckets_6982_, v___x_6988_, v___x_7004_, v_a_6977_);
                crate::leanh::lean_dec_ref(v_buckets_6982_);
                crate::leanh::lean_dec_ref(v___x_6989_);
                if v_isShared_7003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7002_, 0, v___x_7005_);
                    v___x_7007_ = v___x_7002_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 0, v___x_7005_);
                    v___x_7007_ = v_reuseFailAlloc_7008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(
    mut v_pkg_7011_: *mut crate::leanh::LeanObject,
    mut v_a_7012_: *mut crate::leanh::LeanObject,
    mut v_a_7013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7014_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_7011_, v_a_7012_);
    crate::leanh::lean_dec(v_a_7012_);
    crate::leanh::lean_dec(v_pkg_7011_);
    return v_res_7014_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInPackage(
    mut v_pkg_7015_: *mut crate::leanh::LeanObject,
    mut v_a_7016_: *mut crate::leanh::LeanObject,
    mut v_a_7017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7019_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_7015_, v_a_7017_);
    return v___x_7019_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(
    mut v_pkg_7020_: *mut crate::leanh::LeanObject,
    mut v_a_7021_: *mut crate::leanh::LeanObject,
    mut v_a_7022_: *mut crate::leanh::LeanObject,
    mut v_a_7023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7024_ = l_Lean_Linter_EnvLinter_getDeclsInPackage(v_pkg_7020_, v_a_7021_, v_a_7022_);
    crate::leanh::lean_dec(v_a_7022_);
    crate::leanh::lean_dec_ref(v_a_7021_);
    crate::leanh::lean_dec(v_pkg_7020_);
    return v_res_7024_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_EnvLinter_Frontend(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_EnvLinter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Path(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default =
        _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default();
    l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity =
        _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity();
    l_Lean_Linter_EnvLinter_instInhabitedLintScope_default =
        _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope_default();
    l_Lean_Linter_EnvLinter_instInhabitedLintScope =
        _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_EnvLinter_Frontend(
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
pub unsafe fn initialize_Lean_Linter_EnvLinter_Frontend(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_EnvLinter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Path(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_EnvLinter_Frontend(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_EnvLinter_Frontend(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_EnvLinter_Frontend(builtin);
}
