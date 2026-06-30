// Lean compiler output
// Module: Lean.Compiler.IR.CompilerM
// Imports: Lean.Compiler.IR.Format Lean.Compiler.ExportAttr Lean.Compiler.LCNF.PublicDeclsExt Lean.Compiler.InitAttr Lean.Compiler.ModPkgExt Init.Data.Format.Macro Lean.Compiler.LCNF.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr,
    lean_nat_sub, lean_nat_to_int, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_string_length, lean_uint64_of_nat, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_id___boxed,
};
use crate::r#gen::Lean::Compiler::ExportAttr::{
    initialize_Lean_Compiler_ExportAttr, lean_get_export_name_for,
    runtime_initialize_Lean_Compiler_ExportAttr,
};
use crate::r#gen::Lean::Compiler::ExternAttr::l_Lean_isExtern;
use crate::r#gen::Lean::Compiler::IR::Basic::l_Lean_IR_Decl_name;
use crate::r#gen::Lean::Compiler::IR::Format::{
    initialize_Lean_Compiler_IR_Format, l_Lean_IR_formatDecl,
    runtime_initialize_Lean_Compiler_IR_Format,
};
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, l_Lean_regularInitAttr,
    runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Compiler::LCNF::PublicDeclsExt::{
    initialize_Lean_Compiler_LCNF_PublicDeclsExt, l_Lean_Compiler_LCNF_isDeclPublic,
    runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_isBoxedName, l_Lean_Compiler_LCNF_mkBoxedName,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isDeclMeta;
use crate::r#gen::Lean::Compiler::ModPkgExt::{
    initialize_Lean_Compiler_ModPkgExt, l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt,
    runtime_initialize_Lean_Compiler_ModPkgExt,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getEntries___redArg,
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1,
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg, l_Lean_instDecidableEqOLeanLevel,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
pub static l_Lean_IR_LogEntry_fmt___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_Lean_IR_LogEntry_fmt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_LogEntry_fmt___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_IR_LogEntry_fmt___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
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
static mut l_Lean_IR_LogEntry_fmt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_LogEntry_fmt___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_IR_LogEntry_fmt___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_LogEntry_fmt___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_LogEntry_fmt___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_LogEntry_fmt___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_LogEntry_fmt___closed__4_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_LogEntry_fmt___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_LogEntry_fmt___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_LogEntry_fmt___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_IR_LogEntry_fmt___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_LogEntry_fmt___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_LogEntry_fmt___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_LogEntry_fmt___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_IR_LogEntry_instToFormat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_LogEntry_fmt as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_LogEntry_instToFormat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_LogEntry_instToFormat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_IR_LogEntry_instToFormat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_LogEntry_instToFormat___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_IR_log___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0],
    };
static mut l_Lean_IR_log___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_log___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_IR_log___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [73, 82, 0],
    };
static mut l_Lean_IR_log___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_log___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_IR_log___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_IR_log___closed__0_value) as *mut leanh::LeanObject,
            2042452093243897853 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_IR_log___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_IR_log___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_log___closed__1_value) as *mut leanh::LeanObject,
            13893570035957872542 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_log___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_log___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_IR_tracePrefixOptionName___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_IR_tracePrefixOptionName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_IR_tracePrefixOptionName___closed__1_value: leanh::LeanStringObject<9> =
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
        m_data: [99, 111, 109, 112, 105, 108, 101, 114, 0],
    };
static mut l_Lean_IR_tracePrefixOptionName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_IR_tracePrefixOptionName___closed__2_value: leanh::LeanStringObject<3> =
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
static mut l_Lean_IR_tracePrefixOptionName___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__0_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__1_value)
                as *mut leanh::LeanObject,
            5214860269111507234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_IR_tracePrefixOptionName___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__2_value)
                as *mut leanh::LeanObject,
            1999616187639051312 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_tracePrefixOptionName___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_IR_tracePrefixOptionName: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_tracePrefixOptionName___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0_value:
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
    m_fun: l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0_value:
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
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject,807312601722567303 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 99, 108, 77, 97, 112, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_IR_log___closed__1_value) as *mut leanh::LeanObject,896088716302605537 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7673168519149055152 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanClosureObject<4> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value: leanh::LeanCtorObject<7> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_IR_declMapExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_value:
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value:
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_IR_findEnvDecl___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_findEnvDecl___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_getDecl___closed__0_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
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
            117, 110, 107, 110, 111, 119, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 96, 0,
        ],
    };
static mut l_Lean_IR_getDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getDecl___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_IR_getDecl___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
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
static mut l_Lean_IR_getDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getDecl___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_IR_addDecl___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_addDecl___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_addDecl___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_addDecl___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_addDecl___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_addDecl___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_IR_LogEntry_ctorIdx(
    mut v_x_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1893_) == 0 {
        let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1894_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1894_;
    } else {
        let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1895_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1895_;
    }
}
pub unsafe fn l_Lean_IR_LogEntry_ctorIdx___boxed(
    mut v_x_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_IR_LogEntry_ctorIdx(v_x_1896_);
    leanh::lean_dec_ref(v_x_1896_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_IR_LogEntry_ctorElim___redArg(
    mut v_t_1898_: *mut leanh::LeanObject,
    mut v_k_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1898_) == 0 {
        let mut v_cls_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_decls_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cls_1900_ = leanh::lean_ctor_get(v_t_1898_, 0);
        leanh::lean_inc(v_cls_1900_);
        v_decls_1901_ = leanh::lean_ctor_get(v_t_1898_, 1);
        leanh::lean_inc_ref(v_decls_1901_);
        leanh::lean_dec_ref_known(v_t_1898_, 2);
        v___x_1902_ = leanh::lean_apply_2(v_k_1899_, v_cls_1900_, v_decls_1901_);
        return v___x_1902_;
    } else {
        let mut v_msg_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_msg_1903_ = leanh::lean_ctor_get(v_t_1898_, 0);
        leanh::lean_inc(v_msg_1903_);
        leanh::lean_dec_ref_known(v_t_1898_, 1);
        v___x_1904_ = leanh::lean_apply_1(v_k_1899_, v_msg_1903_);
        return v___x_1904_;
    }
}
pub unsafe fn l_Lean_IR_LogEntry_ctorElim(
    mut v_motive_1905_: *mut leanh::LeanObject,
    mut v_ctorIdx_1906_: *mut leanh::LeanObject,
    mut v_t_1907_: *mut leanh::LeanObject,
    mut v_h_1908_: *mut leanh::LeanObject,
    mut v_k_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_1907_, v_k_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_IR_LogEntry_ctorElim___boxed(
    mut v_motive_1911_: *mut leanh::LeanObject,
    mut v_ctorIdx_1912_: *mut leanh::LeanObject,
    mut v_t_1913_: *mut leanh::LeanObject,
    mut v_h_1914_: *mut leanh::LeanObject,
    mut v_k_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ = l_Lean_IR_LogEntry_ctorElim(
        v_motive_1911_,
        v_ctorIdx_1912_,
        v_t_1913_,
        v_h_1914_,
        v_k_1915_,
    );
    leanh::lean_dec(v_ctorIdx_1912_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_IR_LogEntry_step_elim___redArg(
    mut v_t_1917_: *mut leanh::LeanObject,
    mut v_step_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_1917_, v_step_1918_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_IR_LogEntry_step_elim(
    mut v_motive_1920_: *mut leanh::LeanObject,
    mut v_t_1921_: *mut leanh::LeanObject,
    mut v_h_1922_: *mut leanh::LeanObject,
    mut v_step_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_1921_, v_step_1923_);
    return v___x_1924_;
}
pub unsafe fn l_Lean_IR_LogEntry_message_elim___redArg(
    mut v_t_1925_: *mut leanh::LeanObject,
    mut v_message_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_1925_, v_message_1926_);
    return v___x_1927_;
}
pub unsafe fn l_Lean_IR_LogEntry_message_elim(
    mut v_motive_1928_: *mut leanh::LeanObject,
    mut v_t_1929_: *mut leanh::LeanObject,
    mut v_h_1930_: *mut leanh::LeanObject,
    mut v_message_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_1929_, v_message_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Nat_cast___at___00Lean_IR_LogEntry_fmt_spec__0(
    mut v_a_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = lean_nat_to_int(v_a_1933_);
    return v___x_1934_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(
    mut v_as_1935_: *mut leanh::LeanObject,
    mut v_i_1936_: usize,
    mut v_stop_1937_: usize,
    mut v_b_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: usize = 0;
    let mut v___x_1947_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1939_ = lean_usize_dec_eq(v_i_1936_, v_stop_1937_);
                if v___x_1939_ == 0 {
                    v___x_1940_ = lean_array_uget_borrowed(v_as_1935_, v_i_1936_);
                    v___x_1941_ = leanh::lean_box(1);
                    v___x_1942_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1942_, 0, v_b_1938_);
                    leanh::lean_ctor_set(v___x_1942_, 1, v___x_1941_);
                    v___x_1943_ = leanh::lean_unsigned_to_nat(2);
                    leanh::lean_inc(v___x_1940_);
                    v___x_1944_ = l_Lean_IR_formatDecl(v___x_1940_, v___x_1943_);
                    v___x_1945_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1945_, 0, v___x_1942_);
                    leanh::lean_ctor_set(v___x_1945_, 1, v___x_1944_);
                    v___x_1946_ = 1usize;
                    v___x_1947_ = lean_usize_add(v_i_1936_, v___x_1946_);
                    v_i_1936_ = v___x_1947_;
                    v_b_1938_ = v___x_1945_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1938_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1___boxed(
    mut v_as_1949_: *mut leanh::LeanObject,
    mut v_i_1950_: *mut leanh::LeanObject,
    mut v_stop_1951_: *mut leanh::LeanObject,
    mut v_b_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1953_: usize = 0;
    let mut v_stop_boxed_1954_: usize = 0;
    let mut v_res_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1953_ = leanh::lean_unbox_usize(v_i_1950_);
    leanh::lean_dec(v_i_1950_);
    v_stop_boxed_1954_ = leanh::lean_unbox_usize(v_stop_1951_);
    leanh::lean_dec(v_stop_1951_);
    v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_as_1949_, v_i_boxed_1953_, v_stop_boxed_1954_, v_b_1952_);
    leanh::lean_dec_ref(v_as_1949_);
    return v_res_1955_;
}
pub unsafe fn _init_l_Lean_IR_LogEntry_fmt___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_IR_LogEntry_fmt___closed__0;
    v___x_1959_ = lean_string_length(v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn _init_l_Lean_IR_LogEntry_fmt___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_LogEntry_fmt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_IR_LogEntry_fmt___closed__2_once),
        _init_l_Lean_IR_LogEntry_fmt___closed__2,
    );
    v___x_1961_ = lean_nat_to_int(v___x_1960_);
    return v___x_1961_;
}
pub unsafe fn l_Lean_IR_LogEntry_fmt(
    mut v_x_1966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cls_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1972_: u8 = 0;
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: usize = 0;
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_msg_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1966_) == 0 {
                    v_cls_1967_ = leanh::lean_ctor_get(v_x_1966_, 0);
                    v_decls_1968_ = leanh::lean_ctor_get(v_x_1966_, 1);
                    v_isSharedCheck_2000_ = (!leanh::lean_is_exclusive(v_x_1966_)) as u8;
                    if v_isSharedCheck_2000_ == 0 {
                        v___x_1970_ = v_x_1966_;
                        v_isShared_1971_ = v_isSharedCheck_2000_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_decls_1968_);
                        leanh::lean_inc(v_cls_1967_);
                        leanh::lean_dec(v_x_1966_);
                        v___x_1970_ = leanh::lean_box(0);
                        v_isShared_1971_ = v_isSharedCheck_2000_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_msg_2001_ = leanh::lean_ctor_get(v_x_1966_, 0);
                    leanh::lean_inc(v_msg_2001_);
                    leanh::lean_dec_ref_known(v_x_1966_, 1);
                    return v_msg_2001_;
                }
            }
            1 => {
                v___x_1972_ = 1;
                v___x_1973_ = l_Lean_Name_toString(v_cls_1967_, v___x_1972_);
                v___x_1974_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1974_, 0, v___x_1973_);
                v___x_1975_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_LogEntry_fmt___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_IR_LogEntry_fmt___closed__3_once),
                    _init_l_Lean_IR_LogEntry_fmt___closed__3,
                );
                v___x_1976_ = l_Lean_IR_LogEntry_fmt___closed__4;
                if v_isShared_1971_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1970_, 5);
                    leanh::lean_ctor_set(v___x_1970_, 1, v___x_1974_);
                    leanh::lean_ctor_set(v___x_1970_, 0, v___x_1976_);
                    v___x_1978_ = v___x_1970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1974_);
                    v___x_1978_ = v_reuseFailAlloc_1999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1979_ = l_Lean_IR_LogEntry_fmt___closed__5;
                v___x_1980_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1980_, 0, v___x_1978_);
                leanh::lean_ctor_set(v___x_1980_, 1, v___x_1979_);
                v___x_1981_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1981_, 0, v___x_1975_);
                leanh::lean_ctor_set(v___x_1981_, 1, v___x_1980_);
                v___x_1982_ = 0;
                v___x_1983_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1983_, 0, v___x_1981_);
                leanh::lean_ctor_set_uint8(
                    v___x_1983_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1982_,
                );
                v___x_1984_ = leanh::lean_box(0);
                v___x_1985_ = leanh::lean_unsigned_to_nat(0);
                v___x_1986_ = lean_array_get_size(v_decls_1968_);
                v___x_1987_ = lean_nat_dec_lt(v___x_1985_, v___x_1986_);
                if v___x_1987_ == 0 {
                    leanh::lean_dec_ref(v_decls_1968_);
                    v___x_1988_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1988_, 0, v___x_1983_);
                    leanh::lean_ctor_set(v___x_1988_, 1, v___x_1984_);
                    return v___x_1988_;
                } else {
                    v___x_1989_ = lean_nat_dec_le(v___x_1986_, v___x_1986_);
                    if v___x_1989_ == 0 {
                        if v___x_1987_ == 0 {
                            leanh::lean_dec_ref(v_decls_1968_);
                            v___x_1990_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1990_, 0, v___x_1983_);
                            leanh::lean_ctor_set(v___x_1990_, 1, v___x_1984_);
                            return v___x_1990_;
                        } else {
                            v___x_1991_ = 0usize;
                            v___x_1992_ = lean_usize_of_nat(v___x_1986_);
                            v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_1968_, v___x_1991_, v___x_1992_, v___x_1984_);
                            leanh::lean_dec_ref(v_decls_1968_);
                            v___x_1994_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1994_, 0, v___x_1983_);
                            leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                            return v___x_1994_;
                        }
                    } else {
                        v___x_1995_ = 0usize;
                        v___x_1996_ = lean_usize_of_nat(v___x_1986_);
                        v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_1968_, v___x_1995_, v___x_1996_, v___x_1984_);
                        leanh::lean_dec_ref(v_decls_1968_);
                        v___x_1998_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1998_, 0, v___x_1983_);
                        leanh::lean_ctor_set(v___x_1998_, 1, v___x_1997_);
                        return v___x_1998_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(
    mut v_as_2004_: *mut leanh::LeanObject,
    mut v_i_2005_: usize,
    mut v_stop_2006_: usize,
    mut v_b_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: usize = 0;
    let mut v___x_2015_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = lean_usize_dec_eq(v_i_2005_, v_stop_2006_);
                if v___x_2008_ == 0 {
                    v___x_2009_ = lean_array_uget_borrowed(v_as_2004_, v_i_2005_);
                    v___x_2010_ = leanh::lean_box(1);
                    v___x_2011_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2011_, 0, v_b_2007_);
                    leanh::lean_ctor_set(v___x_2011_, 1, v___x_2010_);
                    leanh::lean_inc(v___x_2009_);
                    v___x_2012_ = l_Lean_IR_LogEntry_fmt(v___x_2009_);
                    v___x_2013_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2013_, 0, v___x_2011_);
                    leanh::lean_ctor_set(v___x_2013_, 1, v___x_2012_);
                    v___x_2014_ = 1usize;
                    v___x_2015_ = lean_usize_add(v_i_2005_, v___x_2014_);
                    v_i_2005_ = v___x_2015_;
                    v_b_2007_ = v___x_2013_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2007_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0___boxed(
    mut v_as_2017_: *mut leanh::LeanObject,
    mut v_i_2018_: *mut leanh::LeanObject,
    mut v_stop_2019_: *mut leanh::LeanObject,
    mut v_b_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2021_: usize = 0;
    let mut v_stop_boxed_2022_: usize = 0;
    let mut v_res_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2021_ = leanh::lean_unbox_usize(v_i_2018_);
    leanh::lean_dec(v_i_2018_);
    v_stop_boxed_2022_ = leanh::lean_unbox_usize(v_stop_2019_);
    leanh::lean_dec(v_stop_2019_);
    v_res_2023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_as_2017_, v_i_boxed_2021_, v_stop_boxed_2022_, v_b_2020_);
    leanh::lean_dec_ref(v_as_2017_);
    return v_res_2023_;
}
pub unsafe fn l_Lean_IR_Log_format(
    mut v_log_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    v___x_2025_ = leanh::lean_box(0);
    v___x_2026_ = leanh::lean_unsigned_to_nat(0);
    v___x_2027_ = lean_array_get_size(v_log_2024_);
    v___x_2028_ = lean_nat_dec_lt(v___x_2026_, v___x_2027_);
    if v___x_2028_ == 0 {
        return v___x_2025_;
    } else {
        let mut v___x_2029_: u8 = 0;
        v___x_2029_ = lean_nat_dec_le(v___x_2027_, v___x_2027_);
        if v___x_2029_ == 0 {
            if v___x_2028_ == 0 {
                return v___x_2025_;
            } else {
                let mut v___x_2030_: usize = 0;
                let mut v___x_2031_: usize = 0;
                let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2030_ = 0usize;
                v___x_2031_ = lean_usize_of_nat(v___x_2027_);
                v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_2024_, v___x_2030_, v___x_2031_, v___x_2025_);
                return v___x_2032_;
            }
        } else {
            let mut v___x_2033_: usize = 0;
            let mut v___x_2034_: usize = 0;
            let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2033_ = 0usize;
            v___x_2034_ = lean_usize_of_nat(v___x_2027_);
            v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_2024_, v___x_2033_, v___x_2034_, v___x_2025_);
            return v___x_2035_;
        }
    }
}
pub unsafe fn l_Lean_IR_Log_format___boxed(
    mut v_log_2036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2037_ = l_Lean_IR_Log_format(v_log_2036_);
    leanh::lean_dec_ref(v_log_2036_);
    return v_res_2037_;
}
pub unsafe fn l_Lean_IR_Log_toString(
    mut v_log_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2039_ = l_Lean_IR_Log_format(v_log_2038_);
    v___x_2040_ = l_Std_Format_defWidth;
    v___x_2041_ = leanh::lean_unsigned_to_nat(0);
    v___x_2042_ = l_Std_Format_pretty(v___x_2039_, v___x_2040_, v___x_2041_, v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn l_Lean_IR_Log_toString___boxed(
    mut v_log_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Lean_IR_Log_toString(v_log_2043_);
    leanh::lean_dec_ref(v_log_2043_);
    return v_res_2044_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2045_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2045_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
    v___x_2047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
    return v___x_2047_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
    v___x_2049_ = leanh::lean_unsigned_to_nat(0);
    v___x_2050_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2050_, 0, v___x_2049_);
    leanh::lean_ctor_set(v___x_2050_, 1, v___x_2049_);
    leanh::lean_ctor_set(v___x_2050_, 2, v___x_2049_);
    leanh::lean_ctor_set(v___x_2050_, 3, v___x_2049_);
    leanh::lean_ctor_set(v___x_2050_, 4, v___x_2048_);
    leanh::lean_ctor_set(v___x_2050_, 5, v___x_2048_);
    leanh::lean_ctor_set(v___x_2050_, 6, v___x_2048_);
    leanh::lean_ctor_set(v___x_2050_, 7, v___x_2048_);
    leanh::lean_ctor_set(v___x_2050_, 8, v___x_2048_);
    leanh::lean_ctor_set(v___x_2050_, 9, v___x_2048_);
    return v___x_2050_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = leanh::lean_unsigned_to_nat(32);
    v___x_2052_ = lean_mk_empty_array_with_capacity(v___x_2051_);
    v___x_2053_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2053_, 0, v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2054_ = 5usize;
    v___x_2055_ = leanh::lean_unsigned_to_nat(0);
    v___x_2056_ = leanh::lean_unsigned_to_nat(32);
    v___x_2057_ = lean_mk_empty_array_with_capacity(v___x_2056_);
    v___x_2058_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3);
    v___x_2059_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2059_, 0, v___x_2058_);
    leanh::lean_ctor_set(v___x_2059_, 1, v___x_2057_);
    leanh::lean_ctor_set(v___x_2059_, 2, v___x_2055_);
    leanh::lean_ctor_set(v___x_2059_, 3, v___x_2055_);
    leanh::lean_ctor_set_usize(v___x_2059_, 4, v___x_2054_);
    return v___x_2059_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2060_ = leanh::lean_box(1);
    v___x_2061_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4);
    v___x_2062_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
    v___x_2063_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2063_, 0, v___x_2062_);
    leanh::lean_ctor_set(v___x_2063_, 1, v___x_2061_);
    leanh::lean_ctor_set(v___x_2063_, 2, v___x_2060_);
    return v___x_2063_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(
    mut v_msgData_2064_: *mut leanh::LeanObject,
    mut v___y_2065_: *mut leanh::LeanObject,
    mut v___y_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2068_ = lean_st_ref_get(v___y_2066_);
    v_env_2069_ = leanh::lean_ctor_get(v___x_2068_, 0);
    leanh::lean_inc_ref(v_env_2069_);
    leanh::lean_dec(v___x_2068_);
    v_options_2070_ = leanh::lean_ctor_get(v___y_2065_, 2);
    v___x_2071_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2);
    v___x_2072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_2070_);
    v___x_2073_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2073_, 0, v_env_2069_);
    leanh::lean_ctor_set(v___x_2073_, 1, v___x_2071_);
    leanh::lean_ctor_set(v___x_2073_, 2, v___x_2072_);
    leanh::lean_ctor_set(v___x_2073_, 3, v_options_2070_);
    v___x_2074_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2074_, 0, v___x_2073_);
    leanh::lean_ctor_set(v___x_2074_, 1, v_msgData_2064_);
    v___x_2075_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2075_, 0, v___x_2074_);
    return v___x_2075_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(
    mut v_msgData_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ =
        l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(
            v_msgData_2076_,
            v___y_2077_,
            v___y_2078_,
        );
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    return v_res_2080_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0() -> f64 {
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: f64 = 0.0;
    v___x_2081_ = leanh::lean_unsigned_to_nat(0);
    v___x_2082_ = lean_float_of_nat(v___x_2081_);
    return v___x_2082_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_IR_log_spec__0(
    mut v_cls_2086_: *mut leanh::LeanObject,
    mut v_msg_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2096_: u8 = 0;
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v_tid_2110_: u64 = 0;
    let mut v_traces_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: f64 = 0.0;
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2091_ = leanh::lean_ctor_get(v___y_2088_, 5);
                v___x_2092_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_2087_, v___y_2088_, v___y_2089_);
                v_a_2093_ = leanh::lean_ctor_get(v___x_2092_, 0);
                v_isSharedCheck_2137_ = (!leanh::lean_is_exclusive(v___x_2092_)) as u8;
                if v_isSharedCheck_2137_ == 0 {
                    v___x_2095_ = v___x_2092_;
                    v_isShared_2096_ = v_isSharedCheck_2137_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2093_);
                    leanh::lean_dec(v___x_2092_);
                    v___x_2095_ = leanh::lean_box(0);
                    v_isShared_2096_ = v_isSharedCheck_2137_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2097_ = lean_st_ref_take(v___y_2089_);
                v_traceState_2098_ = leanh::lean_ctor_get(v___x_2097_, 4);
                v_env_2099_ = leanh::lean_ctor_get(v___x_2097_, 0);
                v_nextMacroScope_2100_ = leanh::lean_ctor_get(v___x_2097_, 1);
                v_ngen_2101_ = leanh::lean_ctor_get(v___x_2097_, 2);
                v_auxDeclNGen_2102_ = leanh::lean_ctor_get(v___x_2097_, 3);
                v_cache_2103_ = leanh::lean_ctor_get(v___x_2097_, 5);
                v_messages_2104_ = leanh::lean_ctor_get(v___x_2097_, 6);
                v_infoState_2105_ = leanh::lean_ctor_get(v___x_2097_, 7);
                v_snapshotTasks_2106_ = leanh::lean_ctor_get(v___x_2097_, 8);
                v_isSharedCheck_2136_ = (!leanh::lean_is_exclusive(v___x_2097_)) as u8;
                if v_isSharedCheck_2136_ == 0 {
                    v___x_2108_ = v___x_2097_;
                    v_isShared_2109_ = v_isSharedCheck_2136_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2106_);
                    leanh::lean_inc(v_infoState_2105_);
                    leanh::lean_inc(v_messages_2104_);
                    leanh::lean_inc(v_cache_2103_);
                    leanh::lean_inc(v_traceState_2098_);
                    leanh::lean_inc(v_auxDeclNGen_2102_);
                    leanh::lean_inc(v_ngen_2101_);
                    leanh::lean_inc(v_nextMacroScope_2100_);
                    leanh::lean_inc(v_env_2099_);
                    leanh::lean_dec(v___x_2097_);
                    v___x_2108_ = leanh::lean_box(0);
                    v_isShared_2109_ = v_isSharedCheck_2136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2110_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2098_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2111_ = leanh::lean_ctor_get(v_traceState_2098_, 0);
                v_isSharedCheck_2135_ =
                    (!leanh::lean_is_exclusive(v_traceState_2098_)) as u8;
                if v_isSharedCheck_2135_ == 0 {
                    v___x_2113_ = v_traceState_2098_;
                    v_isShared_2114_ = v_isSharedCheck_2135_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_2111_);
                    leanh::lean_dec(v_traceState_2098_);
                    v___x_2113_ = leanh::lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2115_ = leanh::lean_box(0);
                v___x_2116_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0,
                );
                v___x_2117_ = 0;
                v___x_2118_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1;
                v___x_2119_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_2119_, 0, v_cls_2086_);
                leanh::lean_ctor_set(v___x_2119_, 1, v___x_2115_);
                leanh::lean_ctor_set(v___x_2119_, 2, v___x_2118_);
                leanh::lean_ctor_set_float(
                    v___x_2119_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2116_,
                );
                leanh::lean_ctor_set_float(
                    v___x_2119_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2116_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2119_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2117_,
                );
                v___x_2120_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2;
                v___x_2121_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2121_, 0, v___x_2119_);
                leanh::lean_ctor_set(v___x_2121_, 1, v_a_2093_);
                leanh::lean_ctor_set(v___x_2121_, 2, v___x_2120_);
                leanh::lean_inc(v_ref_2091_);
                v___x_2122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2122_, 0, v_ref_2091_);
                leanh::lean_ctor_set(v___x_2122_, 1, v___x_2121_);
                v___x_2123_ = l_Lean_PersistentArray_push___redArg(v_traces_2111_, v___x_2122_);
                if v_isShared_2114_ == 0 {
                    leanh::lean_ctor_set(v___x_2113_, 0, v___x_2123_);
                    v___x_2125_ = v___x_2113_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2123_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2134_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2110_,
                    );
                    v___x_2125_ = v_reuseFailAlloc_2134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2109_ == 0 {
                    leanh::lean_ctor_set(v___x_2108_, 4, v___x_2125_);
                    v___x_2127_ = v___x_2108_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_env_2099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_nextMacroScope_2100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_ngen_2101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_auxDeclNGen_2102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 4, v___x_2125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 5, v_cache_2103_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 6, v_messages_2104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 7, v_infoState_2105_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 8, v_snapshotTasks_2106_);
                    v___x_2127_ = v_reuseFailAlloc_2133_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2128_ = lean_st_ref_set(v___y_2089_, v___x_2127_);
                v___x_2129_ = leanh::lean_box(0);
                if v_isShared_2096_ == 0 {
                    leanh::lean_ctor_set(v___x_2095_, 0, v___x_2129_);
                    v___x_2131_ = v___x_2095_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2132_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
                    v___x_2131_ = v_reuseFailAlloc_2132_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(
    mut v_cls_2138_: *mut leanh::LeanObject,
    mut v_msg_2139_: *mut leanh::LeanObject,
    mut v___y_2140_: *mut leanh::LeanObject,
    mut v___y_2141_: *mut leanh::LeanObject,
    mut v___y_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(
        v_cls_2138_,
        v_msg_2139_,
        v___y_2140_,
        v___y_2141_,
    );
    leanh::lean_dec(v___y_2141_);
    leanh::lean_dec_ref(v___y_2140_);
    return v_res_2143_;
}
pub unsafe fn l_Lean_IR_log(
    mut v_entry_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Lean_IR_log___closed__2;
    v___x_2154_ = l_Lean_IR_LogEntry_fmt(v_entry_2149_);
    v___x_2155_ = l_Lean_MessageData_ofFormat(v___x_2154_);
    v___x_2156_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(
        v___x_2153_,
        v___x_2155_,
        v_a_2150_,
        v_a_2151_,
    );
    return v___x_2156_;
}
pub unsafe fn l_Lean_IR_log___boxed(
    mut v_entry_2157_: *mut leanh::LeanObject,
    mut v_a_2158_: *mut leanh::LeanObject,
    mut v_a_2159_: *mut leanh::LeanObject,
    mut v_a_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Lean_IR_log(v_entry_2157_, v_a_2158_, v_a_2159_);
    leanh::lean_dec(v_a_2159_);
    leanh::lean_dec_ref(v_a_2158_);
    return v_res_2161_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(
    mut v_opts_2170_: *mut leanh::LeanObject,
    mut v_optName_2171_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_map_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2178_: u8 = 0;
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2172_ = leanh::lean_ctor_get(v_opts_2170_, 0);
                v___x_2179_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2172_, v_optName_2171_);
                if leanh::lean_obj_tag(v___x_2179_) == 1 {
                    v_val_2180_ = leanh::lean_ctor_get(v___x_2179_, 0);
                    leanh::lean_inc(v_val_2180_);
                    leanh::lean_dec_ref_known(v___x_2179_, 1);
                    if leanh::lean_obj_tag(v_val_2180_) == 1 {
                        v_v_2181_ = leanh::lean_ctor_get_uint8(v_val_2180_, 0 as u32);
                        leanh::lean_dec_ref_known(v_val_2180_, 0);
                        return v_v_2181_;
                    } else {
                        leanh::lean_dec(v_val_2180_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2179_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2174_ = l_Lean_IR_tracePrefixOptionName;
                v___x_2175_ = 0;
                v___x_2176_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2172_, v___x_2174_);
                if leanh::lean_obj_tag(v___x_2176_) == 0 {
                    return v___x_2175_;
                } else {
                    v_val_2177_ = leanh::lean_ctor_get(v___x_2176_, 0);
                    leanh::lean_inc(v_val_2177_);
                    leanh::lean_dec_ref_known(v___x_2176_, 1);
                    if leanh::lean_obj_tag(v_val_2177_) == 1 {
                        v_v_2178_ = leanh::lean_ctor_get_uint8(v_val_2177_, 0 as u32);
                        leanh::lean_dec_ref_known(v_val_2177_, 0);
                        return v_v_2178_;
                    } else {
                        leanh::lean_dec(v_val_2177_);
                        return v___x_2175_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(
    mut v_opts_2182_: *mut leanh::LeanObject,
    mut v_optName_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2184_: u8 = 0;
    let mut v_r_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(
        v_opts_2182_,
        v_optName_2183_,
    );
    leanh::lean_dec(v_optName_2183_);
    leanh::lean_dec_ref(v_opts_2182_);
    v_r_2185_ = leanh::lean_box((v_res_2184_) as usize);
    return v_r_2185_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(
    mut v_optName_2186_: *mut leanh::LeanObject,
    mut v_cls_2187_: *mut leanh::LeanObject,
    mut v_decls_2188_: *mut leanh::LeanObject,
    mut v_a_2189_: *mut leanh::LeanObject,
    mut v_a_2190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    v_options_2192_ = leanh::lean_ctor_get(v_a_2189_, 2);
    v___x_2193_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(
        v_options_2192_,
        v_optName_2186_,
    );
    if v___x_2193_ == 0 {
        let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_decls_2188_);
        leanh::lean_dec(v_cls_2187_);
        v___x_2194_ = leanh::lean_box(0);
        v___x_2195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2195_, 0, v___x_2194_);
        return v___x_2195_;
    } else {
        let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2196_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2196_, 0, v_cls_2187_);
        leanh::lean_ctor_set(v___x_2196_, 1, v_decls_2188_);
        v___x_2197_ = l_Lean_IR_log(v___x_2196_, v_a_2189_, v_a_2190_);
        return v___x_2197_;
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(
    mut v_optName_2198_: *mut leanh::LeanObject,
    mut v_cls_2199_: *mut leanh::LeanObject,
    mut v_decls_2200_: *mut leanh::LeanObject,
    mut v_a_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_a_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(
        v_optName_2198_,
        v_cls_2199_,
        v_decls_2200_,
        v_a_2201_,
        v_a_2202_,
    );
    leanh::lean_dec(v_a_2202_);
    leanh::lean_dec_ref(v_a_2201_);
    leanh::lean_dec(v_optName_2198_);
    return v_res_2204_;
}
pub unsafe fn l_Lean_IR_logDecls(
    mut v_cls_2205_: *mut leanh::LeanObject,
    mut v_decl_2206_: *mut leanh::LeanObject,
    mut v_a_2207_: *mut leanh::LeanObject,
    mut v_a_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_Lean_IR_tracePrefixOptionName;
    leanh::lean_inc(v_cls_2205_);
    v___x_2211_ = l_Lean_Name_append(v___x_2210_, v_cls_2205_);
    v___x_2212_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(
        v___x_2211_,
        v_cls_2205_,
        v_decl_2206_,
        v_a_2207_,
        v_a_2208_,
    );
    leanh::lean_dec(v___x_2211_);
    return v___x_2212_;
}
pub unsafe fn l_Lean_IR_logDecls___boxed(
    mut v_cls_2213_: *mut leanh::LeanObject,
    mut v_decl_2214_: *mut leanh::LeanObject,
    mut v_a_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
    mut v_a_2217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2218_ = l_Lean_IR_logDecls(v_cls_2213_, v_decl_2214_, v_a_2215_, v_a_2216_);
    leanh::lean_dec(v_a_2216_);
    leanh::lean_dec_ref(v_a_2215_);
    return v_res_2218_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(
    mut v_inst_2219_: *mut leanh::LeanObject,
    mut v_optName_2220_: *mut leanh::LeanObject,
    mut v_a_2221_: *mut leanh::LeanObject,
    mut v_a_2222_: *mut leanh::LeanObject,
    mut v_a_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    v_options_2225_ = leanh::lean_ctor_get(v_a_2222_, 2);
    v___x_2226_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(
        v_options_2225_,
        v_optName_2220_,
    );
    if v___x_2226_ == 0 {
        let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_2221_);
        leanh::lean_dec_ref(v_inst_2219_);
        v___x_2227_ = leanh::lean_box(0);
        v___x_2228_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2228_, 0, v___x_2227_);
        return v___x_2228_;
    } else {
        let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2229_ = leanh::lean_apply_1(v_inst_2219_, v_a_2221_);
        v___x_2230_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2230_, 0, v___x_2229_);
        v___x_2231_ = l_Lean_IR_log(v___x_2230_, v_a_2222_, v_a_2223_);
        return v___x_2231_;
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(
    mut v_inst_2232_: *mut leanh::LeanObject,
    mut v_optName_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
    mut v_a_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2238_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(
        v_inst_2232_,
        v_optName_2233_,
        v_a_2234_,
        v_a_2235_,
        v_a_2236_,
    );
    leanh::lean_dec(v_a_2236_);
    leanh::lean_dec_ref(v_a_2235_);
    leanh::lean_dec(v_optName_2233_);
    return v_res_2238_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(
    mut v_00_u03b1_2239_: *mut leanh::LeanObject,
    mut v_inst_2240_: *mut leanh::LeanObject,
    mut v_optName_2241_: *mut leanh::LeanObject,
    mut v_a_2242_: *mut leanh::LeanObject,
    mut v_a_2243_: *mut leanh::LeanObject,
    mut v_a_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2246_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(
        v_inst_2240_,
        v_optName_2241_,
        v_a_2242_,
        v_a_2243_,
        v_a_2244_,
    );
    return v___x_2246_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(
    mut v_00_u03b1_2247_: *mut leanh::LeanObject,
    mut v_inst_2248_: *mut leanh::LeanObject,
    mut v_optName_2249_: *mut leanh::LeanObject,
    mut v_a_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
    mut v_a_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(
        v_00_u03b1_2247_,
        v_inst_2248_,
        v_optName_2249_,
        v_a_2250_,
        v_a_2251_,
        v_a_2252_,
    );
    leanh::lean_dec(v_a_2252_);
    leanh::lean_dec_ref(v_a_2251_);
    leanh::lean_dec(v_optName_2249_);
    return v_res_2254_;
}
pub unsafe fn l_Lean_IR_logMessageIf___redArg(
    mut v_inst_2255_: *mut leanh::LeanObject,
    mut v_cls_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = l_Lean_IR_tracePrefixOptionName;
    v___x_2262_ = l_Lean_Name_append(v___x_2261_, v_cls_2256_);
    v___x_2263_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(
        v_inst_2255_,
        v___x_2262_,
        v_a_2257_,
        v_a_2258_,
        v_a_2259_,
    );
    leanh::lean_dec(v___x_2262_);
    return v___x_2263_;
}
pub unsafe fn l_Lean_IR_logMessageIf___redArg___boxed(
    mut v_inst_2264_: *mut leanh::LeanObject,
    mut v_cls_2265_: *mut leanh::LeanObject,
    mut v_a_2266_: *mut leanh::LeanObject,
    mut v_a_2267_: *mut leanh::LeanObject,
    mut v_a_2268_: *mut leanh::LeanObject,
    mut v_a_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2270_ =
        l_Lean_IR_logMessageIf___redArg(v_inst_2264_, v_cls_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
    leanh::lean_dec(v_a_2268_);
    leanh::lean_dec_ref(v_a_2267_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_IR_logMessageIf(
    mut v_00_u03b1_2271_: *mut leanh::LeanObject,
    mut v_inst_2272_: *mut leanh::LeanObject,
    mut v_cls_2273_: *mut leanh::LeanObject,
    mut v_a_2274_: *mut leanh::LeanObject,
    mut v_a_2275_: *mut leanh::LeanObject,
    mut v_a_2276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2278_ = l_Lean_IR_tracePrefixOptionName;
    v___x_2279_ = l_Lean_Name_append(v___x_2278_, v_cls_2273_);
    v___x_2280_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(
        v_inst_2272_,
        v___x_2279_,
        v_a_2274_,
        v_a_2275_,
        v_a_2276_,
    );
    leanh::lean_dec(v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn l_Lean_IR_logMessageIf___boxed(
    mut v_00_u03b1_2281_: *mut leanh::LeanObject,
    mut v_inst_2282_: *mut leanh::LeanObject,
    mut v_cls_2283_: *mut leanh::LeanObject,
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
    mut v_a_2286_: *mut leanh::LeanObject,
    mut v_a_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Lean_IR_logMessageIf(
        v_00_u03b1_2281_,
        v_inst_2282_,
        v_cls_2283_,
        v_a_2284_,
        v_a_2285_,
        v_a_2286_,
    );
    leanh::lean_dec(v_a_2286_);
    leanh::lean_dec_ref(v_a_2285_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_IR_logMessage___redArg(
    mut v_inst_2289_: *mut leanh::LeanObject,
    mut v_a_2290_: *mut leanh::LeanObject,
    mut v_a_2291_: *mut leanh::LeanObject,
    mut v_a_2292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = l_Lean_IR_tracePrefixOptionName;
    v___x_2295_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(
        v_inst_2289_,
        v___x_2294_,
        v_a_2290_,
        v_a_2291_,
        v_a_2292_,
    );
    return v___x_2295_;
}
pub unsafe fn l_Lean_IR_logMessage___redArg___boxed(
    mut v_inst_2296_: *mut leanh::LeanObject,
    mut v_a_2297_: *mut leanh::LeanObject,
    mut v_a_2298_: *mut leanh::LeanObject,
    mut v_a_2299_: *mut leanh::LeanObject,
    mut v_a_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Lean_IR_logMessage___redArg(v_inst_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
    leanh::lean_dec(v_a_2299_);
    leanh::lean_dec_ref(v_a_2298_);
    return v_res_2301_;
}
pub unsafe fn l_Lean_IR_logMessage(
    mut v_00_u03b1_2302_: *mut leanh::LeanObject,
    mut v_inst_2303_: *mut leanh::LeanObject,
    mut v_a_2304_: *mut leanh::LeanObject,
    mut v_a_2305_: *mut leanh::LeanObject,
    mut v_a_2306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = l_Lean_IR_tracePrefixOptionName;
    v___x_2309_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(
        v_inst_2303_,
        v___x_2308_,
        v_a_2304_,
        v_a_2305_,
        v_a_2306_,
    );
    return v___x_2309_;
}
pub unsafe fn l_Lean_IR_logMessage___boxed(
    mut v_00_u03b1_2310_: *mut leanh::LeanObject,
    mut v_inst_2311_: *mut leanh::LeanObject,
    mut v_a_2312_: *mut leanh::LeanObject,
    mut v_a_2313_: *mut leanh::LeanObject,
    mut v_a_2314_: *mut leanh::LeanObject,
    mut v_a_2315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2316_ = l_Lean_IR_logMessage(
        v_00_u03b1_2310_,
        v_inst_2311_,
        v_a_2312_,
        v_a_2313_,
        v_a_2314_,
    );
    leanh::lean_dec(v_a_2314_);
    leanh::lean_dec_ref(v_a_2313_);
    return v_res_2316_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(
    mut v_a_2317_: *mut leanh::LeanObject,
    mut v_b_2318_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: u8 = 0;
    v___x_2319_ = l_Lean_IR_Decl_name(v_a_2317_);
    v___x_2320_ = l_Lean_IR_Decl_name(v_b_2318_);
    v___x_2321_ = l_Lean_Name_quickLt(v___x_2319_, v___x_2320_);
    leanh::lean_dec(v___x_2320_);
    leanh::lean_dec(v___x_2319_);
    return v___x_2321_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(
    mut v_a_2322_: *mut leanh::LeanObject,
    mut v_b_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2324_: u8 = 0;
    let mut v_r_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2324_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_2322_, v_b_2323_);
    leanh::lean_dec_ref(v_b_2323_);
    leanh::lean_dec_ref(v_a_2322_);
    v_r_2325_ = leanh::lean_box((v_res_2324_) as usize);
    return v_r_2325_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(
    mut v_decls_2327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2328_ = lean_array_get_size(v_decls_2327_);
                v___x_2329_ = leanh::lean_unsigned_to_nat(0);
                v___x_2330_ = lean_nat_dec_eq(v___x_2328_, v___x_2329_);
                if v___x_2330_ == 0 {
                    v___x_2331_ =
                        l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
                    v___x_2332_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2333_ = lean_nat_sub(v___x_2328_, v___x_2332_);
                    v___x_2339_ = lean_nat_dec_le(v___x_2329_, v___x_2333_);
                    if v___x_2339_ == 0 {
                        leanh::lean_inc(v___x_2333_);
                        v___y_2335_ = v___x_2333_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2335_ = v___x_2329_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_decls_2327_;
                }
            }
            1 => {
                v___x_2336_ = lean_nat_dec_le(v___y_2335_, v___x_2333_);
                if v___x_2336_ == 0 {
                    leanh::lean_dec(v___x_2333_);
                    leanh::lean_inc(v___y_2335_);
                    v___x_2337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        leanh::lean_box(0),
                        v___x_2331_,
                        v___x_2328_,
                        v_decls_2327_,
                        v___y_2335_,
                        v___y_2335_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    leanh::lean_dec(v___y_2335_);
                    return v___x_2337_;
                } else {
                    v___x_2338_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        leanh::lean_box(0),
                        v___x_2331_,
                        v___x_2328_,
                        v_decls_2327_,
                        v___y_2335_,
                        v___x_2333_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    leanh::lean_dec(v___x_2333_);
                    return v___x_2338_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(
    mut v_decls_2343_: *mut leanh::LeanObject,
    mut v_declName_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    v___x_2345_ = leanh::lean_unsigned_to_nat(0);
    v___x_2346_ = lean_array_get_size(v_decls_2343_);
    v___x_2347_ = lean_nat_dec_lt(v___x_2345_, v___x_2346_);
    if v___x_2347_ == 0 {
        let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_2344_);
        v___x_2348_ = leanh::lean_box(0);
        return v___x_2348_;
    } else {
        let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: u8 = 0;
        v___x_2349_ = leanh::lean_unsigned_to_nat(1);
        v___x_2350_ = lean_nat_sub(v___x_2346_, v___x_2349_);
        v___x_2351_ = lean_nat_dec_le(v___x_2345_, v___x_2350_);
        if v___x_2351_ == 0 {
            let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2350_);
            leanh::lean_dec(v_declName_2344_);
            v___x_2352_ = leanh::lean_box(0);
            return v___x_2352_;
        } else {
            let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tmpDecl_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2353_ =
                l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
            v___x_2354_ = leanh::lean_box(0);
            v___x_2355_ = leanh::lean_box(0);
            v_tmpDecl_2356_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
            leanh::lean_ctor_set(v_tmpDecl_2356_, 0, v_declName_2344_);
            leanh::lean_ctor_set(v_tmpDecl_2356_, 1, v___x_2353_);
            leanh::lean_ctor_set(v_tmpDecl_2356_, 2, v___x_2354_);
            leanh::lean_ctor_set(v_tmpDecl_2356_, 3, v___x_2355_);
            v___x_2357_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
            v___x_2358_ =
                l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1;
            v___x_2359_ = l_Array_binSearchAux___redArg(
                v___x_2357_,
                v___x_2358_,
                v_decls_2343_,
                v_tmpDecl_2356_,
                v___x_2345_,
                v___x_2350_,
            );
            return v___x_2359_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(
    mut v_decls_2360_: *mut leanh::LeanObject,
    mut v_declName_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2362_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(
        v_decls_2360_,
        v_declName_2361_,
    );
    leanh::lean_dec_ref(v_decls_2360_);
    return v_res_2362_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_hi_2363_: *mut leanh::LeanObject,
    mut v_pivot_2364_: *mut leanh::LeanObject,
    mut v_as_2365_: *mut leanh::LeanObject,
    mut v_i_2366_: *mut leanh::LeanObject,
    mut v_k_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2368_ = lean_nat_dec_lt(v_k_2367_, v_hi_2363_);
                if v___x_2368_ == 0 {
                    leanh::lean_dec(v_k_2367_);
                    v___x_2369_ = lean_array_fswap(v_as_2365_, v_i_2366_, v_hi_2363_);
                    v___x_2370_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2370_, 0, v_i_2366_);
                    leanh::lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                    return v___x_2370_;
                } else {
                    v___x_2371_ = lean_array_fget_borrowed(v_as_2365_, v_k_2367_);
                    v___x_2372_ = l_Lean_IR_Decl_name(v___x_2371_);
                    v___x_2373_ = l_Lean_IR_Decl_name(v_pivot_2364_);
                    v___x_2374_ = l_Lean_Name_quickLt(v___x_2372_, v___x_2373_);
                    leanh::lean_dec(v___x_2373_);
                    leanh::lean_dec(v___x_2372_);
                    if v___x_2374_ == 0 {
                        v___x_2375_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2376_ = lean_nat_add(v_k_2367_, v___x_2375_);
                        leanh::lean_dec(v_k_2367_);
                        v_k_2367_ = v___x_2376_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2378_ = lean_array_fswap(v_as_2365_, v_i_2366_, v_k_2367_);
                        v___x_2379_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2380_ = lean_nat_add(v_i_2366_, v___x_2379_);
                        leanh::lean_dec(v_i_2366_);
                        v___x_2381_ = lean_nat_add(v_k_2367_, v___x_2379_);
                        leanh::lean_dec(v_k_2367_);
                        v_as_2365_ = v___x_2378_;
                        v_i_2366_ = v___x_2380_;
                        v_k_2367_ = v___x_2381_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(
    mut v_hi_2383_: *mut leanh::LeanObject,
    mut v_pivot_2384_: *mut leanh::LeanObject,
    mut v_as_2385_: *mut leanh::LeanObject,
    mut v_i_2386_: *mut leanh::LeanObject,
    mut v_k_2387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_2383_, v_pivot_2384_, v_as_2385_, v_i_2386_, v_k_2387_);
    leanh::lean_dec_ref(v_pivot_2384_);
    leanh::lean_dec(v_hi_2383_);
    return v_res_2388_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: u8 = 0;
    v___x_2391_ = l_Lean_IR_Decl_name(v___y_2389_);
    v___x_2392_ = l_Lean_IR_Decl_name(v___y_2390_);
    v___x_2393_ = l_Lean_Name_quickLt(v___x_2391_, v___x_2392_);
    leanh::lean_dec(v___x_2392_);
    leanh::lean_dec(v___x_2391_);
    return v___x_2393_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(
    mut v___y_2394_: *mut leanh::LeanObject,
    mut v___y_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2396_: u8 = 0;
    let mut v_r_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_2394_, v___y_2395_);
    leanh::lean_dec_ref(v___y_2395_);
    leanh::lean_dec_ref(v___y_2394_);
    v_r_2397_ = leanh::lean_box((v_res_2396_) as usize);
    return v_r_2397_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(
    mut v_n_2398_: *mut leanh::LeanObject,
    mut v_as_2399_: *mut leanh::LeanObject,
    mut v_lo_2400_: *mut leanh::LeanObject,
    mut v_hi_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2413_ = lean_nat_dec_lt(v_lo_2400_, v_hi_2401_);
                if v___x_2413_ == 0 {
                    leanh::lean_dec(v_lo_2400_);
                    return v_as_2399_;
                } else {
                    v___x_2414_ = lean_nat_add(v_lo_2400_, v_hi_2401_);
                    v___x_2415_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2416_ = lean_nat_shiftr(v___x_2414_, v___x_2415_);
                    leanh::lean_dec(v___x_2414_);
                    v___x_2429_ = lean_array_fget_borrowed(v_as_2399_, v_mid_2416_);
                    v___x_2430_ = lean_array_fget_borrowed(v_as_2399_, v_lo_2400_);
                    v___x_2431_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_2429_, v___x_2430_);
                    if v___x_2431_ == 0 {
                        v___y_2424_ = v_as_2399_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2432_ = lean_array_fswap(v_as_2399_, v_lo_2400_, v_mid_2416_);
                        v___y_2424_ = v___x_2432_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2404_ = lean_array_fget(v___y_2403_, v_hi_2401_);
                leanh::lean_inc_n(v_lo_2400_, 2);
                v___x_2405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_2401_, v_pivot_2404_, v___y_2403_, v_lo_2400_, v_lo_2400_);
                leanh::lean_dec(v_pivot_2404_);
                v_fst_2406_ = leanh::lean_ctor_get(v___x_2405_, 0);
                leanh::lean_inc(v_fst_2406_);
                v_snd_2407_ = leanh::lean_ctor_get(v___x_2405_, 1);
                leanh::lean_inc(v_snd_2407_);
                leanh::lean_dec_ref(v___x_2405_);
                v___x_2408_ = lean_nat_dec_le(v_hi_2401_, v_fst_2406_);
                if v___x_2408_ == 0 {
                    v___x_2409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_2398_, v_snd_2407_, v_lo_2400_, v_fst_2406_);
                    v___x_2410_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2411_ = lean_nat_add(v_fst_2406_, v___x_2410_);
                    leanh::lean_dec(v_fst_2406_);
                    v_as_2399_ = v___x_2409_;
                    v_lo_2400_ = v___x_2411_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2406_);
                    leanh::lean_dec(v_lo_2400_);
                    return v_snd_2407_;
                }
            }
            2 => {
                v___x_2419_ = lean_array_fget_borrowed(v___y_2418_, v_mid_2416_);
                v___x_2420_ = lean_array_fget_borrowed(v___y_2418_, v_hi_2401_);
                v___x_2421_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_2419_, v___x_2420_);
                if v___x_2421_ == 0 {
                    leanh::lean_dec(v_mid_2416_);
                    v___y_2403_ = v___y_2418_;
                    state = 1;
                    continue;
                } else {
                    v___x_2422_ = lean_array_fswap(v___y_2418_, v_mid_2416_, v_hi_2401_);
                    leanh::lean_dec(v_mid_2416_);
                    v___y_2403_ = v___x_2422_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2425_ = lean_array_fget_borrowed(v___y_2424_, v_hi_2401_);
                v___x_2426_ = lean_array_fget_borrowed(v___y_2424_, v_lo_2400_);
                v___x_2427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_2425_, v___x_2426_);
                if v___x_2427_ == 0 {
                    v___y_2418_ = v___y_2424_;
                    state = 2;
                    continue;
                } else {
                    v___x_2428_ = lean_array_fswap(v___y_2424_, v_lo_2400_, v_hi_2401_);
                    v___y_2418_ = v___x_2428_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_n_2433_: *mut leanh::LeanObject,
    mut v_as_2434_: *mut leanh::LeanObject,
    mut v_lo_2435_: *mut leanh::LeanObject,
    mut v_hi_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_2433_, v_as_2434_, v_lo_2435_, v_hi_2436_);
    leanh::lean_dec(v_hi_2436_);
    leanh::lean_dec(v_n_2433_);
    return v_res_2437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(
    mut v_env_2444_: *mut leanh::LeanObject,
    mut v_as_2445_: *mut leanh::LeanObject,
    mut v_i_2446_: usize,
    mut v_stop_2447_: usize,
    mut v_b_2448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: usize = 0;
    let mut v___y_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: u8 = 0;
    let mut v_f_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: u8 = 0;
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2482_: u8 = 0;
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: u8 = 0;
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2461_ = lean_usize_dec_eq(v_i_2446_, v_stop_2447_);
                if v___x_2461_ == 0 {
                    v___x_2462_ = lean_array_uget_borrowed(v_as_2445_, v_i_2446_);
                    v___x_2479_ = l_Lean_IR_Decl_name(v___x_2462_);
                    leanh::lean_inc_ref(v_env_2444_);
                    v___x_2480_ = l_Lean_isDeclMeta(v_env_2444_, v___x_2479_);
                    if v___x_2480_ == 0 {
                        leanh::lean_inc_ref(v_env_2444_);
                        v___x_2481_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_2444_, v___x_2479_);
                        if v___x_2481_ == 0 {
                            leanh::lean_dec(v___x_2479_);
                            v___y_2450_ = v_b_2448_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2482_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_2479_);
                            if v___x_2482_ == 0 {
                                leanh::lean_dec(v___x_2479_);
                                v___y_2464_ = v___x_2482_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2483_ = l_Lean_Name_getPrefix(v___x_2479_);
                                leanh::lean_dec(v___x_2479_);
                                leanh::lean_inc_ref(v_env_2444_);
                                v___x_2484_ = l_Lean_isExtern(v_env_2444_, v___x_2483_);
                                v___y_2464_ = v___x_2484_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2479_);
                        leanh::lean_inc(v___x_2462_);
                        v___x_2485_ = lean_array_push(v_b_2448_, v___x_2462_);
                        v___y_2450_ = v___x_2485_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2444_);
                    return v_b_2448_;
                }
            }
            1 => {
                v___x_2451_ = 1usize;
                v___x_2452_ = lean_usize_add(v_i_2446_, v___x_2451_);
                v_i_2446_ = v___x_2452_;
                v_b_2448_ = v___y_2450_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__0;
                v___x_2459_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2459_, 0, v___y_2456_);
                leanh::lean_ctor_set(v___x_2459_, 1, v___y_2455_);
                leanh::lean_ctor_set(v___x_2459_, 2, v___y_2457_);
                leanh::lean_ctor_set(v___x_2459_, 3, v___x_2458_);
                v___x_2460_ = lean_array_push(v_b_2448_, v___x_2459_);
                v___y_2450_ = v___x_2460_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_2464_ == 0 {
                    if leanh::lean_obj_tag(v___x_2462_) == 0 {
                        v_f_2465_ = leanh::lean_ctor_get(v___x_2462_, 0);
                        v_xs_2466_ = leanh::lean_ctor_get(v___x_2462_, 1);
                        v_type_2467_ = leanh::lean_ctor_get(v___x_2462_, 2);
                        leanh::lean_inc(v_f_2465_);
                        leanh::lean_inc_ref(v_env_2444_);
                        v___x_2468_ = lean_get_export_name_for(v_env_2444_, v_f_2465_);
                        if leanh::lean_obj_tag(v___x_2468_) == 1 {
                            v_val_2469_ = leanh::lean_ctor_get(v___x_2468_, 0);
                            leanh::lean_inc(v_val_2469_);
                            leanh::lean_dec_ref_known(v___x_2468_, 1);
                            if leanh::lean_obj_tag(v_val_2469_) == 1 {
                                v_str_2470_ = leanh::lean_ctor_get(v_val_2469_, 1);
                                leanh::lean_inc_ref(v_str_2470_);
                                leanh::lean_dec_ref_known(v_val_2469_, 2);
                                v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___closed__2;
                                v___x_2472_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2472_, 0, v___x_2471_);
                                leanh::lean_ctor_set(v___x_2472_, 1, v_str_2470_);
                                v___x_2473_ = leanh::lean_box(0);
                                v___x_2474_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2474_, 0, v___x_2472_);
                                leanh::lean_ctor_set(v___x_2474_, 1, v___x_2473_);
                                leanh::lean_inc(v_type_2467_);
                                leanh::lean_inc_ref(v_xs_2466_);
                                leanh::lean_inc(v_f_2465_);
                                v___x_2475_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                                leanh::lean_ctor_set(v___x_2475_, 0, v_f_2465_);
                                leanh::lean_ctor_set(v___x_2475_, 1, v_xs_2466_);
                                leanh::lean_ctor_set(v___x_2475_, 2, v_type_2467_);
                                leanh::lean_ctor_set(v___x_2475_, 3, v___x_2474_);
                                v___x_2476_ = lean_array_push(v_b_2448_, v___x_2475_);
                                v___y_2450_ = v___x_2476_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_2469_);
                                leanh::lean_inc(v_type_2467_);
                                leanh::lean_inc(v_f_2465_);
                                leanh::lean_inc_ref(v_xs_2466_);
                                v___y_2455_ = v_xs_2466_;
                                v___y_2456_ = v_f_2465_;
                                v___y_2457_ = v_type_2467_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2468_);
                            leanh::lean_inc(v_type_2467_);
                            leanh::lean_inc(v_f_2465_);
                            leanh::lean_inc_ref(v_xs_2466_);
                            v___y_2455_ = v_xs_2466_;
                            v___y_2456_ = v_f_2465_;
                            v___y_2457_ = v_type_2467_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v___x_2462_);
                        v___x_2477_ = lean_array_push(v_b_2448_, v___x_2462_);
                        v___y_2450_ = v___x_2477_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___x_2462_);
                    v___x_2478_ = lean_array_push(v_b_2448_, v___x_2462_);
                    v___y_2450_ = v___x_2478_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_env_2486_: *mut leanh::LeanObject,
    mut v_as_2487_: *mut leanh::LeanObject,
    mut v_i_2488_: *mut leanh::LeanObject,
    mut v_stop_2489_: *mut leanh::LeanObject,
    mut v_b_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2491_: usize = 0;
    let mut v_stop_boxed_2492_: usize = 0;
    let mut v_res_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2491_ = leanh::lean_unbox_usize(v_i_2488_);
    leanh::lean_dec(v_i_2488_);
    v_stop_boxed_2492_ = leanh::lean_unbox_usize(v_stop_2489_);
    leanh::lean_dec(v_stop_2489_);
    v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_2486_, v_as_2487_, v_i_boxed_2491_, v_stop_boxed_2492_, v_b_2490_);
    leanh::lean_dec_ref(v_as_2487_);
    return v_res_2493_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(
    mut v_env_2496_: *mut leanh::LeanObject,
    mut v_as_2497_: *mut leanh::LeanObject,
    mut v_start_2498_: *mut leanh::LeanObject,
    mut v_stop_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: u8 = 0;
    v___x_2500_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0;
    v___x_2501_ = lean_nat_dec_lt(v_start_2498_, v_stop_2499_);
    if v___x_2501_ == 0 {
        leanh::lean_dec_ref(v_env_2496_);
        return v___x_2500_;
    } else {
        let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2503_: u8 = 0;
        v___x_2502_ = lean_array_get_size(v_as_2497_);
        v___x_2503_ = lean_nat_dec_le(v_stop_2499_, v___x_2502_);
        if v___x_2503_ == 0 {
            let mut v___x_2504_: u8 = 0;
            v___x_2504_ = lean_nat_dec_lt(v_start_2498_, v___x_2502_);
            if v___x_2504_ == 0 {
                leanh::lean_dec_ref(v_env_2496_);
                return v___x_2500_;
            } else {
                let mut v___x_2505_: usize = 0;
                let mut v___x_2506_: usize = 0;
                let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2505_ = lean_usize_of_nat(v_start_2498_);
                v___x_2506_ = lean_usize_of_nat(v___x_2502_);
                v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_2496_, v_as_2497_, v___x_2505_, v___x_2506_, v___x_2500_);
                return v___x_2507_;
            }
        } else {
            let mut v___x_2508_: usize = 0;
            let mut v___x_2509_: usize = 0;
            let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2508_ = lean_usize_of_nat(v_start_2498_);
            v___x_2509_ = lean_usize_of_nat(v_stop_2499_);
            v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0_spec__0(v_env_2496_, v_as_2497_, v___x_2508_, v___x_2509_, v___x_2500_);
            return v___x_2510_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___boxed(
    mut v_env_2511_: *mut leanh::LeanObject,
    mut v_as_2512_: *mut leanh::LeanObject,
    mut v_start_2513_: *mut leanh::LeanObject,
    mut v_stop_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_2511_, v_as_2512_, v_start_2513_, v_stop_2514_);
    leanh::lean_dec(v_stop_2514_);
    leanh::lean_dec(v_start_2513_);
    leanh::lean_dec_ref(v_as_2512_);
    return v_res_2515_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(
    mut v_x_2516_: *mut leanh::LeanObject,
    mut v_x_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2517_) == 0 {
                    return v_x_2516_;
                } else {
                    v_head_2518_ = leanh::lean_ctor_get(v_x_2517_, 0);
                    leanh::lean_inc(v_head_2518_);
                    v_tail_2519_ = leanh::lean_ctor_get(v_x_2517_, 1);
                    leanh::lean_inc(v_tail_2519_);
                    leanh::lean_dec_ref_known(v_x_2517_, 2);
                    v___x_2520_ = lean_array_push(v_x_2516_, v_head_2518_);
                    v_x_2516_ = v___x_2520_;
                    v_x_2517_ = v_tail_2519_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(
    mut v_env_2522_: *mut leanh::LeanObject,
    mut v_s_2523_: *mut leanh::LeanObject,
    mut v_entries_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_2528_: u8 = 0;
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2534_ = leanh::lean_unsigned_to_nat(0);
                v___x_2535_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0;
                v_decls_2536_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_2535_, v_entries_2524_);
                v___x_2537_ = lean_array_get_size(v_decls_2536_);
                v___x_2542_ = lean_nat_dec_eq(v___x_2537_, v___x_2534_);
                if v___x_2542_ == 0 {
                    v___x_2543_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2544_ = lean_nat_sub(v___x_2537_, v___x_2543_);
                    v___x_2548_ = lean_nat_dec_le(v___x_2534_, v___x_2544_);
                    if v___x_2548_ == 0 {
                        leanh::lean_inc(v___x_2544_);
                        v___y_2546_ = v___x_2544_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2546_ = v___x_2534_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_2526_ = v_decls_2536_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2527_ = l_Lean_Environment_header(v_env_2522_);
                v_isModule_2528_ = leanh::lean_ctor_get_uint8(
                    v___x_2527_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                leanh::lean_dec_ref(v___x_2527_);
                if v_isModule_2528_ == 0 {
                    leanh::lean_dec_ref(v_env_2522_);
                    leanh::lean_inc_ref_n(v___y_2526_, 2);
                    v___x_2529_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2529_, 0, v___y_2526_);
                    leanh::lean_ctor_set(v___x_2529_, 1, v___y_2526_);
                    leanh::lean_ctor_set(v___x_2529_, 2, v___y_2526_);
                    return v___x_2529_;
                } else {
                    v___x_2530_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2531_ = lean_array_get_size(v___y_2526_);
                    v___x_2532_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0(v_env_2522_, v___y_2526_, v___x_2530_, v___x_2531_);
                    leanh::lean_dec_ref(v___y_2526_);
                    leanh::lean_inc_ref_n(v___x_2532_, 2);
                    v___x_2533_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2533_, 0, v___x_2532_);
                    leanh::lean_ctor_set(v___x_2533_, 1, v___x_2532_);
                    leanh::lean_ctor_set(v___x_2533_, 2, v___x_2532_);
                    return v___x_2533_;
                }
            }
            2 => {
                v___x_2541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_2537_, v_decls_2536_, v___y_2539_, v___y_2540_);
                leanh::lean_dec(v___y_2540_);
                v___y_2526_ = v___x_2541_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2547_ = lean_nat_dec_le(v___y_2546_, v___x_2544_);
                if v___x_2547_ == 0 {
                    leanh::lean_dec(v___x_2544_);
                    leanh::lean_inc(v___y_2546_);
                    v___y_2539_ = v___y_2546_;
                    v___y_2540_ = v___y_2546_;
                    state = 2;
                    continue;
                } else {
                    v___y_2539_ = v___y_2546_;
                    v___y_2540_ = v___x_2544_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(
    mut v_env_2549_: *mut leanh::LeanObject,
    mut v_s_2550_: *mut leanh::LeanObject,
    mut v_entries_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2552_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_env_2549_, v_s_2550_, v_entries_2551_);
    leanh::lean_dec_ref(v_s_2550_);
    return v_res_2552_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(
    mut v_es_2553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = lean_array_mk(v_es_2553_);
    return v___x_2554_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(
    mut v_keys_2555_: *mut leanh::LeanObject,
    mut v_i_2556_: *mut leanh::LeanObject,
    mut v_k_2557_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v_k_x27_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2558_ = lean_array_get_size(v_keys_2555_);
                v___x_2559_ = lean_nat_dec_lt(v_i_2556_, v___x_2558_);
                if v___x_2559_ == 0 {
                    leanh::lean_dec(v_i_2556_);
                    return v___x_2559_;
                } else {
                    v_k_x27_2560_ = lean_array_fget_borrowed(v_keys_2555_, v_i_2556_);
                    v___x_2561_ = lean_name_eq(v_k_2557_, v_k_x27_2560_);
                    if v___x_2561_ == 0 {
                        v___x_2562_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2563_ = lean_nat_add(v_i_2556_, v___x_2562_);
                        leanh::lean_dec(v_i_2556_);
                        v_i_2556_ = v___x_2563_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_2556_);
                        return v___x_2561_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg___boxed(
    mut v_keys_2565_: *mut leanh::LeanObject,
    mut v_i_2566_: *mut leanh::LeanObject,
    mut v_k_2567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2568_: u8 = 0;
    let mut v_r_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_2565_, v_i_2566_, v_k_2567_);
    leanh::lean_dec(v_k_2567_);
    leanh::lean_dec_ref(v_keys_2565_);
    v_r_2569_ = leanh::lean_box((v_res_2568_) as usize);
    return v_r_2569_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_2570_: usize = 0;
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    v___x_2570_ = 5usize;
    v___x_2571_ = 1usize;
    v___x_2572_ = lean_usize_shift_left(v___x_2571_, v___x_2570_);
    return v___x_2572_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_2573_: usize = 0;
    let mut v___x_2574_: usize = 0;
    let mut v___x_2575_: usize = 0;
    v___x_2573_ = 1usize;
    v___x_2574_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
    v___x_2575_ = lean_usize_sub(v___x_2574_, v___x_2573_);
    return v___x_2575_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(
    mut v_x_2576_: *mut leanh::LeanObject,
    mut v_x_2577_: usize,
    mut v_x_2578_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: usize = 0;
    let mut v___x_2582_: usize = 0;
    let mut v___x_2583_: usize = 0;
    let mut v_j_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u8 = 0;
    let mut v_node_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: usize = 0;
    let mut v___x_2591_: u8 = 0;
    let mut v_ks_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2576_) == 0 {
                    v_es_2579_ = leanh::lean_ctor_get(v_x_2576_, 0);
                    v___x_2580_ = leanh::lean_box(2);
                    v___x_2581_ = 5usize;
                    v___x_2582_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
                    v___x_2583_ = lean_usize_land(v_x_2577_, v___x_2582_);
                    v_j_2584_ = lean_usize_to_nat(v___x_2583_);
                    v___x_2585_ = lean_array_get_borrowed(v___x_2580_, v_es_2579_, v_j_2584_);
                    leanh::lean_dec(v_j_2584_);
                    match leanh::lean_obj_tag(v___x_2585_) {
                        0 => {
                            v_key_2586_ = leanh::lean_ctor_get(v___x_2585_, 0);
                            v___x_2587_ = lean_name_eq(v_x_2578_, v_key_2586_);
                            return v___x_2587_;
                        }
                        1 => {
                            v_node_2588_ = leanh::lean_ctor_get(v___x_2585_, 0);
                            v___x_2589_ = lean_usize_shift_right(v_x_2577_, v___x_2581_);
                            v_x_2576_ = v_node_2588_;
                            v_x_2577_ = v___x_2589_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2591_ = 0;
                            return v___x_2591_;
                        }
                    }
                } else {
                    v_ks_2592_ = leanh::lean_ctor_get(v_x_2576_, 0);
                    v___x_2593_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2594_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_ks_2592_, v___x_2593_, v_x_2578_);
                    return v___x_2594_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(
    mut v_x_2595_: *mut leanh::LeanObject,
    mut v_x_2596_: *mut leanh::LeanObject,
    mut v_x_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2626__boxed_2598_: usize = 0;
    let mut v_res_2599_: u8 = 0;
    let mut v_r_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2626__boxed_2598_ = leanh::lean_unbox_usize(v_x_2596_);
    leanh::lean_dec(v_x_2596_);
    v_res_2599_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_2595_, v_x_2626__boxed_2598_, v_x_2597_);
    leanh::lean_dec(v_x_2597_);
    leanh::lean_dec_ref(v_x_2595_);
    v_r_2600_ = leanh::lean_box((v_res_2599_) as usize);
    return v_r_2600_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: u64 = 0;
    v___x_2601_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2602_ = lean_uint64_of_nat(v___x_2601_);
    return v___x_2602_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(
    mut v_x_2603_: *mut leanh::LeanObject,
    mut v_x_2604_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_2606_: u64 = 0;
    let mut v___x_2607_: usize = 0;
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2609_: u64 = 0;
    let mut v_hash_2610_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2604_) == 0 {
                    v___x_2609_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
                    v___y_2606_ = v___x_2609_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2610_ = leanh::lean_ctor_get_uint64(
                        v_x_2604_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2606_ = v_hash_2610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2607_ = lean_uint64_to_usize(v___y_2606_);
                v___x_2608_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_2603_, v___x_2607_, v_x_2604_);
                return v___x_2608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___boxed(
    mut v_x_2611_: *mut leanh::LeanObject,
    mut v_x_2612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2613_: u8 = 0;
    let mut v_r_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2613_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_2611_, v_x_2612_);
    leanh::lean_dec(v_x_2612_);
    leanh::lean_dec_ref(v_x_2611_);
    v_r_2614_ = leanh::lean_box((v_res_2613_) as usize);
    return v_r_2614_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(
    mut v_x1_2615_: *mut leanh::LeanObject,
    mut v_x2_2616_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: u8 = 0;
    v___x_2617_ = l_Lean_IR_Decl_name(v_x2_2616_);
    v___x_2618_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x1_2615_, v___x_2617_);
    leanh::lean_dec(v___x_2617_);
    if v___x_2618_ == 0 {
        let mut v___x_2619_: u8 = 0;
        v___x_2619_ = 1;
        return v___x_2619_;
    } else {
        let mut v___x_2620_: u8 = 0;
        v___x_2620_ = 0;
        return v___x_2620_;
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(
    mut v_x1_2621_: *mut leanh::LeanObject,
    mut v_x2_2622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2623_: u8 = 0;
    let mut v_r_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2623_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x1_2621_, v_x2_2622_);
    leanh::lean_dec_ref(v_x2_2622_);
    leanh::lean_dec_ref(v_x1_2621_);
    v_r_2624_ = leanh::lean_box((v_res_2623_) as usize);
    return v_r_2624_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2625_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
    v___x_2627_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2627_, 0, v___x_2626_);
    return v___x_2627_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(
    mut v_x_2628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_);
    return v___x_2629_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(
    mut v_x_2630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2631_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(v_x_2630_);
    leanh::lean_dec_ref(v_x_2630_);
    return v_res_2631_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(
    mut v_x_2632_: *mut leanh::LeanObject,
    mut v_x_2633_: *mut leanh::LeanObject,
    mut v_x_2634_: *mut leanh::LeanObject,
    mut v_x_2635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2640_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2636_ = leanh::lean_ctor_get(v_x_2632_, 0);
                v_vs_2637_ = leanh::lean_ctor_get(v_x_2632_, 1);
                v_isSharedCheck_2661_ = (!leanh::lean_is_exclusive(v_x_2632_)) as u8;
                if v_isSharedCheck_2661_ == 0 {
                    v___x_2639_ = v_x_2632_;
                    v_isShared_2640_ = v_isSharedCheck_2661_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2637_);
                    leanh::lean_inc(v_ks_2636_);
                    leanh::lean_dec(v_x_2632_);
                    v___x_2639_ = leanh::lean_box(0);
                    v_isShared_2640_ = v_isSharedCheck_2661_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2641_ = lean_array_get_size(v_ks_2636_);
                v___x_2642_ = lean_nat_dec_lt(v_x_2633_, v___x_2641_);
                if v___x_2642_ == 0 {
                    leanh::lean_dec(v_x_2633_);
                    v___x_2643_ = lean_array_push(v_ks_2636_, v_x_2634_);
                    v___x_2644_ = lean_array_push(v_vs_2637_, v_x_2635_);
                    if v_isShared_2640_ == 0 {
                        leanh::lean_ctor_set(v___x_2639_, 1, v___x_2644_);
                        leanh::lean_ctor_set(v___x_2639_, 0, v___x_2643_);
                        v___x_2646_ = v___x_2639_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2647_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2643_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2644_);
                        v___x_2646_ = v_reuseFailAlloc_2647_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2648_ = lean_array_fget_borrowed(v_ks_2636_, v_x_2633_);
                    v___x_2649_ = lean_name_eq(v_x_2634_, v_k_x27_2648_);
                    if v___x_2649_ == 0 {
                        if v_isShared_2640_ == 0 {
                            v___x_2651_ = v___x_2639_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2655_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_ks_2636_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_vs_2637_);
                            v___x_2651_ = v_reuseFailAlloc_2655_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2656_ = lean_array_fset(v_ks_2636_, v_x_2633_, v_x_2634_);
                        v___x_2657_ = lean_array_fset(v_vs_2637_, v_x_2633_, v_x_2635_);
                        leanh::lean_dec(v_x_2633_);
                        if v_isShared_2640_ == 0 {
                            leanh::lean_ctor_set(v___x_2639_, 1, v___x_2657_);
                            leanh::lean_ctor_set(v___x_2639_, 0, v___x_2656_);
                            v___x_2659_ = v___x_2639_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2660_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2656_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2657_);
                            v___x_2659_ = v_reuseFailAlloc_2660_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2646_;
            }
            3 => {
                v___x_2652_ = leanh::lean_unsigned_to_nat(1);
                v___x_2653_ = lean_nat_add(v_x_2633_, v___x_2652_);
                leanh::lean_dec(v_x_2633_);
                v_x_2632_ = v___x_2651_;
                v_x_2633_ = v___x_2653_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(
    mut v_n_2662_: *mut leanh::LeanObject,
    mut v_k_2663_: *mut leanh::LeanObject,
    mut v_v_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = leanh::lean_unsigned_to_nat(0);
    v___x_2666_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_n_2662_, v___x_2665_, v_k_2663_, v_v_2664_);
    return v___x_2666_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2667_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(
    mut v_x_2668_: *mut leanh::LeanObject,
    mut v_x_2669_: usize,
    mut v_x_2670_: usize,
    mut v_x_2671_: *mut leanh::LeanObject,
    mut v_x_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: usize = 0;
    let mut v___x_2675_: usize = 0;
    let mut v___x_2676_: usize = 0;
    let mut v___x_2677_: usize = 0;
    let mut v_j_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: u8 = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v_v_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_node_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2708_: u8 = 0;
    let mut v___x_2709_: usize = 0;
    let mut v___x_2710_: usize = 0;
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2717_: u8 = 0;
    let mut v_unused_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: u8 = 0;
    let mut v_ks_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: usize = 0;
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: u8 = 0;
    let mut v_reuseFailAlloc_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2668_) == 0 {
                    v_es_2673_ = leanh::lean_ctor_get(v_x_2668_, 0);
                    v___x_2674_ = 5usize;
                    v___x_2675_ = 1usize;
                    v___x_2676_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
                    v___x_2677_ = lean_usize_land(v_x_2669_, v___x_2676_);
                    v_j_2678_ = lean_usize_to_nat(v___x_2677_);
                    v___x_2679_ = lean_array_get_size(v_es_2673_);
                    v___x_2680_ = lean_nat_dec_lt(v_j_2678_, v___x_2679_);
                    if v___x_2680_ == 0 {
                        leanh::lean_dec(v_j_2678_);
                        leanh::lean_dec(v_x_2672_);
                        leanh::lean_dec(v_x_2671_);
                        return v_x_2668_;
                    } else {
                        leanh::lean_inc_ref(v_es_2673_);
                        v_isSharedCheck_2717_ = (!leanh::lean_is_exclusive(v_x_2668_)) as u8;
                        if v_isSharedCheck_2717_ == 0 {
                            v_unused_2718_ = leanh::lean_ctor_get(v_x_2668_, 0);
                            leanh::lean_dec(v_unused_2718_);
                            v___x_2682_ = v_x_2668_;
                            v_isShared_2683_ = v_isSharedCheck_2717_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2668_);
                            v___x_2682_ = leanh::lean_box(0);
                            v_isShared_2683_ = v_isSharedCheck_2717_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2719_ = leanh::lean_ctor_get(v_x_2668_, 0);
                    v_vs_2720_ = leanh::lean_ctor_get(v_x_2668_, 1);
                    v_isSharedCheck_2740_ = (!leanh::lean_is_exclusive(v_x_2668_)) as u8;
                    if v_isSharedCheck_2740_ == 0 {
                        v___x_2722_ = v_x_2668_;
                        v_isShared_2723_ = v_isSharedCheck_2740_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2720_);
                        leanh::lean_inc(v_ks_2719_);
                        leanh::lean_dec(v_x_2668_);
                        v___x_2722_ = leanh::lean_box(0);
                        v_isShared_2723_ = v_isSharedCheck_2740_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2684_ = lean_array_fget(v_es_2673_, v_j_2678_);
                v___x_2685_ = leanh::lean_box(0);
                v_xs_x27_2686_ = lean_array_fset(v_es_2673_, v_j_2678_, v___x_2685_);
                match leanh::lean_obj_tag(v_v_2684_) {
                    0 => {
                        v_key_2693_ = leanh::lean_ctor_get(v_v_2684_, 0);
                        v_val_2694_ = leanh::lean_ctor_get(v_v_2684_, 1);
                        v_isSharedCheck_2704_ = (!leanh::lean_is_exclusive(v_v_2684_)) as u8;
                        if v_isSharedCheck_2704_ == 0 {
                            v___x_2696_ = v_v_2684_;
                            v_isShared_2697_ = v_isSharedCheck_2704_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2694_);
                            leanh::lean_inc(v_key_2693_);
                            leanh::lean_dec(v_v_2684_);
                            v___x_2696_ = leanh::lean_box(0);
                            v_isShared_2697_ = v_isSharedCheck_2704_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2705_ = leanh::lean_ctor_get(v_v_2684_, 0);
                        v_isSharedCheck_2715_ = (!leanh::lean_is_exclusive(v_v_2684_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2707_ = v_v_2684_;
                            v_isShared_2708_ = v_isSharedCheck_2715_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2705_);
                            leanh::lean_dec(v_v_2684_);
                            v___x_2707_ = leanh::lean_box(0);
                            v_isShared_2708_ = v_isSharedCheck_2715_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2716_, 0, v_x_2671_);
                        leanh::lean_ctor_set(v___x_2716_, 1, v_x_2672_);
                        v___y_2688_ = v___x_2716_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2689_ = lean_array_fset(v_xs_x27_2686_, v_j_2678_, v___y_2688_);
                leanh::lean_dec(v_j_2678_);
                if v_isShared_2683_ == 0 {
                    leanh::lean_ctor_set(v___x_2682_, 0, v___x_2689_);
                    v___x_2691_ = v___x_2682_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
                    v___x_2691_ = v_reuseFailAlloc_2692_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2691_;
            }
            4 => {
                v___x_2698_ = lean_name_eq(v_x_2671_, v_key_2693_);
                if v___x_2698_ == 0 {
                    leanh::lean_del_object(v___x_2696_);
                    v___x_2699_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2693_,
                        v_val_2694_,
                        v_x_2671_,
                        v_x_2672_,
                    );
                    v___x_2700_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2700_, 0, v___x_2699_);
                    v___y_2688_ = v___x_2700_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2694_);
                    leanh::lean_dec(v_key_2693_);
                    if v_isShared_2697_ == 0 {
                        leanh::lean_ctor_set(v___x_2696_, 1, v_x_2672_);
                        leanh::lean_ctor_set(v___x_2696_, 0, v_x_2671_);
                        v___x_2702_ = v___x_2696_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2703_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_x_2671_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_x_2672_);
                        v___x_2702_ = v_reuseFailAlloc_2703_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2688_ = v___x_2702_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2709_ = lean_usize_shift_right(v_x_2669_, v___x_2674_);
                v___x_2710_ = lean_usize_add(v_x_2670_, v___x_2675_);
                v___x_2711_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_node_2705_, v___x_2709_, v___x_2710_, v_x_2671_, v_x_2672_);
                if v_isShared_2708_ == 0 {
                    leanh::lean_ctor_set(v___x_2707_, 0, v___x_2711_);
                    v___x_2713_ = v___x_2707_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2711_);
                    v___x_2713_ = v_reuseFailAlloc_2714_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2688_ = v___x_2713_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2723_ == 0 {
                    v___x_2725_ = v___x_2722_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2739_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_ks_2719_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_vs_2720_);
                    v___x_2725_ = v_reuseFailAlloc_2739_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2726_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v___x_2725_, v_x_2671_, v_x_2672_);
                v___x_2734_ = 7usize;
                v___x_2735_ = lean_usize_dec_le(v___x_2734_, v_x_2670_);
                if v___x_2735_ == 0 {
                    v___x_2736_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2726_);
                    v___x_2737_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2738_ = lean_nat_dec_lt(v___x_2736_, v___x_2737_);
                    leanh::lean_dec(v___x_2736_);
                    v___y_2728_ = v___x_2738_;
                    state = 10;
                    continue;
                } else {
                    v___y_2728_ = v___x_2735_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2728_ == 0 {
                    v_ks_2729_ = leanh::lean_ctor_get(v_newNode_2726_, 0);
                    leanh::lean_inc_ref(v_ks_2729_);
                    v_vs_2730_ = leanh::lean_ctor_get(v_newNode_2726_, 1);
                    leanh::lean_inc_ref(v_vs_2730_);
                    leanh::lean_dec_ref(v_newNode_2726_);
                    v___x_2731_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2732_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___closed__0);
                    v___x_2733_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_x_2670_, v_ks_2729_, v_vs_2730_, v___x_2731_, v___x_2732_);
                    leanh::lean_dec_ref(v_vs_2730_);
                    leanh::lean_dec_ref(v_ks_2729_);
                    return v___x_2733_;
                } else {
                    return v_newNode_2726_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(
    mut v_depth_2741_: usize,
    mut v_keys_2742_: *mut leanh::LeanObject,
    mut v_vals_2743_: *mut leanh::LeanObject,
    mut v_i_2744_: *mut leanh::LeanObject,
    mut v_entries_2745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: u8 = 0;
    let mut v_k_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2751_: u64 = 0;
    let mut v_h_2752_: usize = 0;
    let mut v___x_2753_: usize = 0;
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: usize = 0;
    let mut v___x_2756_: usize = 0;
    let mut v___x_2757_: usize = 0;
    let mut v_h_2758_: usize = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u64 = 0;
    let mut v_hash_2763_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = lean_array_get_size(v_keys_2742_);
                v___x_2747_ = lean_nat_dec_lt(v_i_2744_, v___x_2746_);
                if v___x_2747_ == 0 {
                    leanh::lean_dec(v_i_2744_);
                    return v_entries_2745_;
                } else {
                    v_k_2748_ = lean_array_fget_borrowed(v_keys_2742_, v_i_2744_);
                    v_v_2749_ = lean_array_fget_borrowed(v_vals_2743_, v_i_2744_);
                    if leanh::lean_obj_tag(v_k_2748_) == 0 {
                        v___x_2762_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
                        v___y_2751_ = v___x_2762_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2763_ = leanh::lean_ctor_get_uint64(
                            v_k_2748_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2751_ = v_hash_2763_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2752_ = lean_uint64_to_usize(v___y_2751_);
                v___x_2753_ = 5usize;
                v___x_2754_ = leanh::lean_unsigned_to_nat(1);
                v___x_2755_ = 1usize;
                v___x_2756_ = lean_usize_sub(v_depth_2741_, v___x_2755_);
                v___x_2757_ = lean_usize_mul(v___x_2753_, v___x_2756_);
                v_h_2758_ = lean_usize_shift_right(v_h_2752_, v___x_2757_);
                v___x_2759_ = lean_nat_add(v_i_2744_, v___x_2754_);
                leanh::lean_dec(v_i_2744_);
                leanh::lean_inc(v_v_2749_);
                leanh::lean_inc(v_k_2748_);
                v___x_2760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_entries_2745_, v_h_2758_, v_depth_2741_, v_k_2748_, v_v_2749_);
                v_i_2744_ = v___x_2759_;
                v_entries_2745_ = v___x_2760_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg___boxed(
    mut v_depth_2764_: *mut leanh::LeanObject,
    mut v_keys_2765_: *mut leanh::LeanObject,
    mut v_vals_2766_: *mut leanh::LeanObject,
    mut v_i_2767_: *mut leanh::LeanObject,
    mut v_entries_2768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2769_: usize = 0;
    let mut v_res_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2769_ = leanh::lean_unbox_usize(v_depth_2764_);
    leanh::lean_dec(v_depth_2764_);
    v_res_2770_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_boxed_2769_, v_keys_2765_, v_vals_2766_, v_i_2767_, v_entries_2768_);
    leanh::lean_dec_ref(v_vals_2766_);
    leanh::lean_dec_ref(v_keys_2765_);
    return v_res_2770_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg___boxed(
    mut v_x_2771_: *mut leanh::LeanObject,
    mut v_x_2772_: *mut leanh::LeanObject,
    mut v_x_2773_: *mut leanh::LeanObject,
    mut v_x_2774_: *mut leanh::LeanObject,
    mut v_x_2775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2810__boxed_2776_: usize = 0;
    let mut v_x_2811__boxed_2777_: usize = 0;
    let mut v_res_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2810__boxed_2776_ = leanh::lean_unbox_usize(v_x_2772_);
    leanh::lean_dec(v_x_2772_);
    v_x_2811__boxed_2777_ = leanh::lean_unbox_usize(v_x_2773_);
    leanh::lean_dec(v_x_2773_);
    v_res_2778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_2771_, v_x_2810__boxed_2776_, v_x_2811__boxed_2777_, v_x_2774_, v_x_2775_);
    return v_res_2778_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(
    mut v_x_2779_: *mut leanh::LeanObject,
    mut v_x_2780_: *mut leanh::LeanObject,
    mut v_x_2781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2783_: u64 = 0;
    let mut v___x_2784_: usize = 0;
    let mut v___x_2785_: usize = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u64 = 0;
    let mut v_hash_2788_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2780_) == 0 {
                    v___x_2787_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
                    v___y_2783_ = v___x_2787_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2788_ = leanh::lean_ctor_get_uint64(
                        v_x_2780_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2783_ = v_hash_2788_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2784_ = lean_uint64_to_usize(v___y_2783_);
                v___x_2785_ = 1usize;
                v___x_2786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_2779_, v___x_2784_, v___x_2785_, v_x_2780_, v_x_2781_);
                return v___x_2786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_(
    mut v_s_2789_: *mut leanh::LeanObject,
    mut v_d_2790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = l_Lean_IR_Decl_name(v_d_2790_);
    v___x_2792_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_s_2789_, v___x_2791_, v_d_2790_);
    return v___x_2792_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2820_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_;
    v___x_2821_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2820_);
    return v___x_2821_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2____boxed(
    mut v_a_2822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2823_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
    return v_res_2823_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(
    mut v_n_2824_: *mut leanh::LeanObject,
    mut v_as_2825_: *mut leanh::LeanObject,
    mut v_lo_2826_: *mut leanh::LeanObject,
    mut v_hi_2827_: *mut leanh::LeanObject,
    mut v_w_2828_: *mut leanh::LeanObject,
    mut v_hlo_2829_: *mut leanh::LeanObject,
    mut v_hhi_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v_n_2824_, v_as_2825_, v_lo_2826_, v_hi_2827_);
    return v___x_2831_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___boxed(
    mut v_n_2832_: *mut leanh::LeanObject,
    mut v_as_2833_: *mut leanh::LeanObject,
    mut v_lo_2834_: *mut leanh::LeanObject,
    mut v_hi_2835_: *mut leanh::LeanObject,
    mut v_w_2836_: *mut leanh::LeanObject,
    mut v_hlo_2837_: *mut leanh::LeanObject,
    mut v_hhi_2838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2(v_n_2832_, v_as_2833_, v_lo_2834_, v_hi_2835_, v_w_2836_, v_hlo_2837_, v_hhi_2838_);
    leanh::lean_dec(v_hi_2835_);
    leanh::lean_dec(v_n_2832_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(
    mut v_00_u03b2_2840_: *mut leanh::LeanObject,
    mut v_x_2841_: *mut leanh::LeanObject,
    mut v_x_2842_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2843_: u8 = 0;
    v___x_2843_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v_x_2841_, v_x_2842_);
    return v___x_2843_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___boxed(
    mut v_00_u03b2_2844_: *mut leanh::LeanObject,
    mut v_x_2845_: *mut leanh::LeanObject,
    mut v_x_2846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2847_: u8 = 0;
    let mut v_r_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2847_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3(v_00_u03b2_2844_, v_x_2845_, v_x_2846_);
    leanh::lean_dec(v_x_2846_);
    leanh::lean_dec_ref(v_x_2845_);
    v_r_2848_ = leanh::lean_box((v_res_2847_) as usize);
    return v_r_2848_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4(
    mut v_00_u03b2_2849_: *mut leanh::LeanObject,
    mut v_x_2850_: *mut leanh::LeanObject,
    mut v_x_2851_: *mut leanh::LeanObject,
    mut v_x_2852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4___redArg(v_x_2850_, v_x_2851_, v_x_2852_);
    return v___x_2853_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(
    mut v_n_2854_: *mut leanh::LeanObject,
    mut v_lo_2855_: *mut leanh::LeanObject,
    mut v_hi_2856_: *mut leanh::LeanObject,
    mut v_hhi_2857_: *mut leanh::LeanObject,
    mut v_pivot_2858_: *mut leanh::LeanObject,
    mut v_as_2859_: *mut leanh::LeanObject,
    mut v_i_2860_: *mut leanh::LeanObject,
    mut v_k_2861_: *mut leanh::LeanObject,
    mut v_ilo_2862_: *mut leanh::LeanObject,
    mut v_ik_2863_: *mut leanh::LeanObject,
    mut v_w_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_2856_, v_pivot_2858_, v_as_2859_, v_i_2860_, v_k_2861_);
    return v___x_2865_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_n_2866_: *mut leanh::LeanObject,
    mut v_lo_2867_: *mut leanh::LeanObject,
    mut v_hi_2868_: *mut leanh::LeanObject,
    mut v_hhi_2869_: *mut leanh::LeanObject,
    mut v_pivot_2870_: *mut leanh::LeanObject,
    mut v_as_2871_: *mut leanh::LeanObject,
    mut v_i_2872_: *mut leanh::LeanObject,
    mut v_k_2873_: *mut leanh::LeanObject,
    mut v_ilo_2874_: *mut leanh::LeanObject,
    mut v_ik_2875_: *mut leanh::LeanObject,
    mut v_w_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2_spec__3(v_n_2866_, v_lo_2867_, v_hi_2868_, v_hhi_2869_, v_pivot_2870_, v_as_2871_, v_i_2872_, v_k_2873_, v_ilo_2874_, v_ik_2875_, v_w_2876_);
    leanh::lean_dec_ref(v_pivot_2870_);
    leanh::lean_dec(v_hi_2868_);
    leanh::lean_dec(v_lo_2867_);
    leanh::lean_dec(v_n_2866_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(
    mut v_00_u03b2_2878_: *mut leanh::LeanObject,
    mut v_x_2879_: *mut leanh::LeanObject,
    mut v_x_2880_: usize,
    mut v_x_2881_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2882_: u8 = 0;
    v___x_2882_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_2879_, v_x_2880_, v_x_2881_);
    return v___x_2882_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___boxed(
    mut v_00_u03b2_2883_: *mut leanh::LeanObject,
    mut v_x_2884_: *mut leanh::LeanObject,
    mut v_x_2885_: *mut leanh::LeanObject,
    mut v_x_2886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3099__boxed_2887_: usize = 0;
    let mut v_res_2888_: u8 = 0;
    let mut v_r_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3099__boxed_2887_ = leanh::lean_unbox_usize(v_x_2885_);
    leanh::lean_dec(v_x_2885_);
    v_res_2888_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_2883_, v_x_2884_, v_x_3099__boxed_2887_, v_x_2886_);
    leanh::lean_dec(v_x_2886_);
    leanh::lean_dec_ref(v_x_2884_);
    v_r_2889_ = leanh::lean_box((v_res_2888_) as usize);
    return v_r_2889_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(
    mut v_00_u03b2_2890_: *mut leanh::LeanObject,
    mut v_x_2891_: *mut leanh::LeanObject,
    mut v_x_2892_: usize,
    mut v_x_2893_: usize,
    mut v_x_2894_: *mut leanh::LeanObject,
    mut v_x_2895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___redArg(v_x_2891_, v_x_2892_, v_x_2893_, v_x_2894_, v_x_2895_);
    return v___x_2896_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7___boxed(
    mut v_00_u03b2_2897_: *mut leanh::LeanObject,
    mut v_x_2898_: *mut leanh::LeanObject,
    mut v_x_2899_: *mut leanh::LeanObject,
    mut v_x_2900_: *mut leanh::LeanObject,
    mut v_x_2901_: *mut leanh::LeanObject,
    mut v_x_2902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3110__boxed_2903_: usize = 0;
    let mut v_x_3111__boxed_2904_: usize = 0;
    let mut v_res_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3110__boxed_2903_ = leanh::lean_unbox_usize(v_x_2899_);
    leanh::lean_dec(v_x_2899_);
    v_x_3111__boxed_2904_ = leanh::lean_unbox_usize(v_x_2900_);
    leanh::lean_dec(v_x_2900_);
    v_res_2905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7(v_00_u03b2_2897_, v_x_2898_, v_x_3110__boxed_2903_, v_x_3111__boxed_2904_, v_x_2901_, v_x_2902_);
    return v_res_2905_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(
    mut v_00_u03b2_2906_: *mut leanh::LeanObject,
    mut v_keys_2907_: *mut leanh::LeanObject,
    mut v_vals_2908_: *mut leanh::LeanObject,
    mut v_heq_2909_: *mut leanh::LeanObject,
    mut v_i_2910_: *mut leanh::LeanObject,
    mut v_k_2911_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2912_: u8 = 0;
    v___x_2912_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___redArg(v_keys_2907_, v_i_2910_, v_k_2911_);
    return v___x_2912_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6___boxed(
    mut v_00_u03b2_2913_: *mut leanh::LeanObject,
    mut v_keys_2914_: *mut leanh::LeanObject,
    mut v_vals_2915_: *mut leanh::LeanObject,
    mut v_heq_2916_: *mut leanh::LeanObject,
    mut v_i_2917_: *mut leanh::LeanObject,
    mut v_k_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2919_: u8 = 0;
    let mut v_r_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2919_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5_spec__6(v_00_u03b2_2913_, v_keys_2914_, v_vals_2915_, v_heq_2916_, v_i_2917_, v_k_2918_);
    leanh::lean_dec(v_k_2918_);
    leanh::lean_dec_ref(v_vals_2915_);
    leanh::lean_dec_ref(v_keys_2914_);
    v_r_2920_ = leanh::lean_box((v_res_2919_) as usize);
    return v_r_2920_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9(
    mut v_00_u03b2_2921_: *mut leanh::LeanObject,
    mut v_n_2922_: *mut leanh::LeanObject,
    mut v_k_2923_: *mut leanh::LeanObject,
    mut v_v_2924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2925_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9___redArg(v_n_2922_, v_k_2923_, v_v_2924_);
    return v___x_2925_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(
    mut v_00_u03b2_2926_: *mut leanh::LeanObject,
    mut v_depth_2927_: usize,
    mut v_keys_2928_: *mut leanh::LeanObject,
    mut v_vals_2929_: *mut leanh::LeanObject,
    mut v_heq_2930_: *mut leanh::LeanObject,
    mut v_i_2931_: *mut leanh::LeanObject,
    mut v_entries_2932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___redArg(v_depth_2927_, v_keys_2928_, v_vals_2929_, v_i_2931_, v_entries_2932_);
    return v___x_2933_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10___boxed(
    mut v_00_u03b2_2934_: *mut leanh::LeanObject,
    mut v_depth_2935_: *mut leanh::LeanObject,
    mut v_keys_2936_: *mut leanh::LeanObject,
    mut v_vals_2937_: *mut leanh::LeanObject,
    mut v_heq_2938_: *mut leanh::LeanObject,
    mut v_i_2939_: *mut leanh::LeanObject,
    mut v_entries_2940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2941_: usize = 0;
    let mut v_res_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2941_ = leanh::lean_unbox_usize(v_depth_2935_);
    leanh::lean_dec(v_depth_2935_);
    v_res_2942_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__10(v_00_u03b2_2934_, v_depth_boxed_2941_, v_keys_2936_, v_vals_2937_, v_heq_2938_, v_i_2939_, v_entries_2940_);
    leanh::lean_dec_ref(v_vals_2937_);
    leanh::lean_dec_ref(v_keys_2936_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10(
    mut v_00_u03b2_2943_: *mut leanh::LeanObject,
    mut v_x_2944_: *mut leanh::LeanObject,
    mut v_x_2945_: *mut leanh::LeanObject,
    mut v_x_2946_: *mut leanh::LeanObject,
    mut v_x_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__4_spec__7_spec__9_spec__10___redArg(v_x_2944_, v_x_2945_, v_x_2946_, v_x_2947_);
    return v___x_2948_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(
    mut v_irDecls_2949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: u8 = 0;
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2950_ = lean_array_get_size(v_irDecls_2949_);
                v___x_2951_ = leanh::lean_unsigned_to_nat(0);
                v___x_2952_ = lean_nat_dec_eq(v___x_2950_, v___x_2951_);
                if v___x_2952_ == 0 {
                    v___x_2953_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2954_ = lean_nat_sub(v___x_2950_, v___x_2953_);
                    v___x_2960_ = lean_nat_dec_le(v___x_2951_, v___x_2954_);
                    if v___x_2960_ == 0 {
                        leanh::lean_inc(v___x_2954_);
                        v___y_2956_ = v___x_2954_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2956_ = v___x_2951_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_irDecls_2949_;
                }
            }
            1 => {
                v___x_2957_ = lean_nat_dec_le(v___y_2956_, v___x_2954_);
                if v___x_2957_ == 0 {
                    leanh::lean_dec(v___x_2954_);
                    leanh::lean_inc(v___y_2956_);
                    v___x_2958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_2950_, v_irDecls_2949_, v___y_2956_, v___y_2956_);
                    leanh::lean_dec(v___y_2956_);
                    return v___x_2958_;
                } else {
                    v___x_2959_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg(v___x_2950_, v_irDecls_2949_, v___y_2956_, v___x_2954_);
                    leanh::lean_dec(v___x_2954_);
                    return v___x_2959_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(
    mut v_initDecls_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_initDecls_2961_);
    return v_initDecls_2961_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(
    mut v_initDecls_2962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2963_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(
        v_initDecls_2962_,
    );
    leanh::lean_dec_ref(v_initDecls_2962_);
    return v_res_2963_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(
    mut v_modPkg_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_modPkg_2964_);
    return v_modPkg_2964_;
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(
    mut v_modPkg_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2966_ =
        l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_2965_);
    leanh::lean_dec_ref(v_modPkg_2965_);
    return v_res_2966_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2969_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1;
    v___x_2970_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0;
    v___x_2971_ = l_Lean_PersistentHashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2970_,
        v___x_2969_,
    );
    return v___x_2971_;
}
pub unsafe fn lean_ir_export_entries(
    mut v_env_2975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_private_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_private_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDecls_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irEntries_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = l_Lean_IR_declMapExt;
    v_toEnvExtension_2977_ = leanh::lean_ctor_get(v___x_2976_, 0);
    v_name_2978_ = leanh::lean_ctor_get(v___x_2976_, 1);
    v_asyncMode_2979_ = leanh::lean_ctor_get(v_toEnvExtension_2977_, 2);
    v___x_2980_ = l_Lean_regularInitAttr;
    v_ext_2981_ = leanh::lean_ctor_get(v___x_2980_, 1);
    v_toEnvExtension_2982_ = leanh::lean_ctor_get(v_ext_2981_, 0);
    v_name_2983_ = leanh::lean_ctor_get(v_ext_2981_, 1);
    v_exportEntriesFn_2984_ = leanh::lean_ctor_get(v_ext_2981_, 4);
    v_asyncMode_2985_ = leanh::lean_ctor_get(v_toEnvExtension_2982_, 2);
    v___x_2986_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once
        ),
        _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2,
    );
    v___x_2987_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
    leanh::lean_inc_ref_n(v_env_2975_, 4);
    v___x_2988_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v___x_2986_,
        v___x_2976_,
        v_env_2975_,
        v_asyncMode_2979_,
    );
    v___x_2989_ = leanh::lean_box(0);
    v___x_2990_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2987_,
        v_ext_2981_,
        v_env_2975_,
        v_asyncMode_2985_,
        v___x_2989_,
    );
    leanh::lean_inc_ref(v_exportEntriesFn_2984_);
    v___x_2991_ = leanh::lean_apply_2(v_exportEntriesFn_2984_, v_env_2975_, v___x_2990_);
    v_private_2992_ = leanh::lean_ctor_get(v___x_2991_, 2);
    leanh::lean_inc(v_private_2992_);
    leanh::lean_dec_ref(v___x_2991_);
    v___x_2993_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
    v_toEnvExtension_2994_ = leanh::lean_ctor_get(v___x_2993_, 0);
    v_name_2995_ = leanh::lean_ctor_get(v___x_2993_, 1);
    v_exportEntriesFn_2996_ = leanh::lean_ctor_get(v___x_2993_, 4);
    v_asyncMode_2997_ = leanh::lean_ctor_get(v_toEnvExtension_2994_, 2);
    v___x_2998_ = leanh::lean_box(0);
    v___x_2999_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2998_,
        v___x_2993_,
        v_env_2975_,
        v_asyncMode_2997_,
        v___x_2989_,
    );
    leanh::lean_inc_ref(v_exportEntriesFn_2996_);
    v___x_3000_ = leanh::lean_apply_2(v_exportEntriesFn_2996_, v_env_2975_, v___x_2999_);
    v_private_3001_ = leanh::lean_ctor_get(v___x_3000_, 2);
    leanh::lean_inc(v_private_3001_);
    leanh::lean_dec_ref(v___x_3000_);
    v___x_3002_ = l_Array_filterMapM___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__0___closed__0;
    v_irDecls_3003_ = l_List_foldl___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__1(v___x_3002_, v___x_2988_);
    v_irEntries_3004_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(
        v_irDecls_3003_,
    );
    leanh::lean_inc(v_name_2978_);
    v___x_3005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3005_, 0, v_name_2978_);
    leanh::lean_ctor_set(v___x_3005_, 1, v_irEntries_3004_);
    leanh::lean_inc(v_name_2983_);
    v___x_3006_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3006_, 0, v_name_2983_);
    leanh::lean_ctor_set(v___x_3006_, 1, v_private_2992_);
    leanh::lean_inc(v_name_2995_);
    v___x_3007_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3007_, 0, v_name_2995_);
    leanh::lean_ctor_set(v___x_3007_, 1, v_private_3001_);
    v___x_3008_ = leanh::lean_unsigned_to_nat(3);
    v___x_3009_ = lean_mk_empty_array_with_capacity(v___x_3008_);
    v___x_3010_ = lean_array_push(v___x_3009_, v___x_3005_);
    v___x_3011_ = lean_array_push(v___x_3010_, v___x_3006_);
    v___x_3012_ = lean_array_push(v___x_3011_, v___x_3007_);
    return v___x_3012_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
    mut v_as_3013_: *mut leanh::LeanObject,
    mut v_k_3014_: *mut leanh::LeanObject,
    mut v_x_3015_: *mut leanh::LeanObject,
    mut v_x_3016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: u8 = 0;
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3017_ = lean_nat_add(v_x_3015_, v_x_3016_);
                v___x_3018_ = leanh::lean_unsigned_to_nat(1);
                v_m_3019_ = lean_nat_shiftr(v___x_3017_, v___x_3018_);
                leanh::lean_dec(v___x_3017_);
                v_a_3020_ = lean_array_fget_borrowed(v_as_3013_, v_m_3019_);
                v___x_3021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_3020_, v_k_3014_);
                if v___x_3021_ == 0 {
                    leanh::lean_dec(v_x_3016_);
                    v___x_3022_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_3014_, v_a_3020_);
                    if v___x_3022_ == 0 {
                        leanh::lean_dec(v_m_3019_);
                        leanh::lean_dec(v_x_3015_);
                        leanh::lean_inc(v_a_3020_);
                        v___x_3023_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3023_, 0, v_a_3020_);
                        return v___x_3023_;
                    } else {
                        v___x_3024_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3025_ = lean_nat_dec_eq(v_m_3019_, v___x_3024_);
                        if v___x_3025_ == 0 {
                            v___x_3026_ = lean_nat_sub(v_m_3019_, v___x_3018_);
                            leanh::lean_dec(v_m_3019_);
                            v___x_3027_ = lean_nat_dec_lt(v___x_3026_, v_x_3015_);
                            if v___x_3027_ == 0 {
                                v_x_3016_ = v___x_3026_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3026_);
                                leanh::lean_dec(v_x_3015_);
                                v___x_3029_ = leanh::lean_box(0);
                                return v___x_3029_;
                            }
                        } else {
                            leanh::lean_dec(v_m_3019_);
                            leanh::lean_dec(v_x_3015_);
                            v___x_3030_ = leanh::lean_box(0);
                            return v___x_3030_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_3015_);
                    v___x_3031_ = lean_nat_add(v_m_3019_, v___x_3018_);
                    leanh::lean_dec(v_m_3019_);
                    v___x_3032_ = lean_nat_dec_le(v___x_3031_, v_x_3016_);
                    if v___x_3032_ == 0 {
                        leanh::lean_dec(v___x_3031_);
                        leanh::lean_dec(v_x_3016_);
                        v___x_3033_ = leanh::lean_box(0);
                        return v___x_3033_;
                    } else {
                        v_x_3015_ = v___x_3031_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(
    mut v_as_3035_: *mut leanh::LeanObject,
    mut v_k_3036_: *mut leanh::LeanObject,
    mut v_x_3037_: *mut leanh::LeanObject,
    mut v_x_3038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3039_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
        v_as_3035_, v_k_3036_, v_x_3037_, v_x_3038_,
    );
    leanh::lean_dec_ref(v_k_3036_);
    leanh::lean_dec_ref(v_as_3035_);
    return v_res_3039_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3040_: *mut leanh::LeanObject,
    mut v_vals_3041_: *mut leanh::LeanObject,
    mut v_i_3042_: *mut leanh::LeanObject,
    mut v_k_3043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: u8 = 0;
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3044_ = lean_array_get_size(v_keys_3040_);
                v___x_3045_ = lean_nat_dec_lt(v_i_3042_, v___x_3044_);
                if v___x_3045_ == 0 {
                    leanh::lean_dec(v_i_3042_);
                    v___x_3046_ = leanh::lean_box(0);
                    return v___x_3046_;
                } else {
                    v_k_x27_3047_ = lean_array_fget_borrowed(v_keys_3040_, v_i_3042_);
                    v___x_3048_ = lean_name_eq(v_k_3043_, v_k_x27_3047_);
                    if v___x_3048_ == 0 {
                        v___x_3049_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3050_ = lean_nat_add(v_i_3042_, v___x_3049_);
                        leanh::lean_dec(v_i_3042_);
                        v_i_3042_ = v___x_3050_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3052_ = lean_array_fget_borrowed(v_vals_3041_, v_i_3042_);
                        leanh::lean_dec(v_i_3042_);
                        leanh::lean_inc(v___x_3052_);
                        v___x_3053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3053_, 0, v___x_3052_);
                        return v___x_3053_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3054_: *mut leanh::LeanObject,
    mut v_vals_3055_: *mut leanh::LeanObject,
    mut v_i_3056_: *mut leanh::LeanObject,
    mut v_k_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_3054_, v_vals_3055_, v_i_3056_, v_k_3057_);
    leanh::lean_dec(v_k_3057_);
    leanh::lean_dec_ref(v_vals_3055_);
    leanh::lean_dec_ref(v_keys_3054_);
    return v_res_3058_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(
    mut v_x_3059_: *mut leanh::LeanObject,
    mut v_x_3060_: usize,
    mut v_x_3061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: usize = 0;
    let mut v___x_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v_j_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: usize = 0;
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3059_) == 0 {
                    v_es_3062_ = leanh::lean_ctor_get(v_x_3059_, 0);
                    v___x_3063_ = leanh::lean_box(2);
                    v___x_3064_ = 5usize;
                    v___x_3065_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
                    v___x_3066_ = lean_usize_land(v_x_3060_, v___x_3065_);
                    v_j_3067_ = lean_usize_to_nat(v___x_3066_);
                    v___x_3068_ = lean_array_get_borrowed(v___x_3063_, v_es_3062_, v_j_3067_);
                    leanh::lean_dec(v_j_3067_);
                    match leanh::lean_obj_tag(v___x_3068_) {
                        0 => {
                            v_key_3069_ = leanh::lean_ctor_get(v___x_3068_, 0);
                            v_val_3070_ = leanh::lean_ctor_get(v___x_3068_, 1);
                            v___x_3071_ = lean_name_eq(v_x_3061_, v_key_3069_);
                            if v___x_3071_ == 0 {
                                v___x_3072_ = leanh::lean_box(0);
                                return v___x_3072_;
                            } else {
                                leanh::lean_inc(v_val_3070_);
                                v___x_3073_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3073_, 0, v_val_3070_);
                                return v___x_3073_;
                            }
                        }
                        1 => {
                            v_node_3074_ = leanh::lean_ctor_get(v___x_3068_, 0);
                            v___x_3075_ = lean_usize_shift_right(v_x_3060_, v___x_3064_);
                            v_x_3059_ = v_node_3074_;
                            v_x_3060_ = v___x_3075_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3077_ = leanh::lean_box(0);
                            return v___x_3077_;
                        }
                    }
                } else {
                    v_ks_3078_ = leanh::lean_ctor_get(v_x_3059_, 0);
                    v_vs_3079_ = leanh::lean_ctor_get(v_x_3059_, 1);
                    v___x_3080_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3081_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_3078_, v_vs_3079_, v___x_3080_, v_x_3061_);
                    return v___x_3081_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(
    mut v_x_3082_: *mut leanh::LeanObject,
    mut v_x_3083_: *mut leanh::LeanObject,
    mut v_x_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_416__boxed_3085_: usize = 0;
    let mut v_res_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_416__boxed_3085_ = leanh::lean_unbox_usize(v_x_3083_);
    leanh::lean_dec(v_x_3083_);
    v_res_3086_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_3082_, v_x_416__boxed_3085_, v_x_3084_);
    leanh::lean_dec(v_x_3084_);
    leanh::lean_dec_ref(v_x_3082_);
    return v_res_3086_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(
    mut v_x_3087_: *mut leanh::LeanObject,
    mut v_x_3088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3090_: u64 = 0;
    let mut v___x_3091_: usize = 0;
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u64 = 0;
    let mut v_hash_3094_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3088_) == 0 {
                    v___x_3093_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg___closed__0);
                    v___y_3090_ = v___x_3093_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3094_ = leanh::lean_ctor_get_uint64(
                        v_x_3088_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3090_ = v_hash_3094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3091_ = lean_uint64_to_usize(v___y_3090_);
                v___x_3092_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_3087_, v___x_3091_, v_x_3088_);
                return v___x_3092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(
    mut v_x_3095_: *mut leanh::LeanObject,
    mut v_x_3096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(
        v_x_3095_, v_x_3096_,
    );
    leanh::lean_dec(v_x_3096_);
    leanh::lean_dec_ref(v_x_3095_);
    return v_res_3097_;
}
pub unsafe fn _init_l_Lean_IR_findEnvDecl___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3098_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once
        ),
        _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2,
    );
    v___x_3099_ = leanh::lean_box(0);
    v___x_3100_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3100_, 0, v___x_3099_);
    leanh::lean_ctor_set(v___x_3100_, 1, v___x_3098_);
    return v___x_3100_;
}
pub unsafe fn l_Lean_IR_findEnvDecl(
    mut v_env_3101_: *mut leanh::LeanObject,
    mut v_declName_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: u8 = 0;
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: u8 = 0;
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: u8 = 0;
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3103_ = leanh::lean_box(0);
                v___x_3104_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_findEnvDecl___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_IR_findEnvDecl___closed__0_once),
                    _init_l_Lean_IR_findEnvDecl___closed__0,
                );
                v___x_3105_ = l_Lean_IR_declMapExt;
                v___x_3113_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3101_, v_declName_3102_);
                if leanh::lean_obj_tag(v___x_3113_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_3114_ = leanh::lean_ctor_get(v___x_3113_, 0);
                    leanh::lean_inc(v_val_3114_);
                    leanh::lean_dec_ref_known(v___x_3113_, 1);
                    v___x_3128_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3104_, v___x_3105_, v_env_3101_, v_val_3114_);
                    v___x_3129_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3130_ = lean_array_get_size(v___x_3128_);
                    v___x_3131_ = lean_nat_dec_lt(v___x_3129_, v___x_3130_);
                    if v___x_3131_ == 0 {
                        leanh::lean_dec_ref(v___x_3128_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3132_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3133_ = lean_nat_sub(v___x_3130_, v___x_3132_);
                        v___x_3134_ = lean_nat_dec_le(v___x_3129_, v___x_3133_);
                        if v___x_3134_ == 0 {
                            leanh::lean_dec(v___x_3133_);
                            leanh::lean_dec_ref(v___x_3128_);
                            state = 2;
                            continue;
                        } else {
                            v___x_3135_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
                            v___x_3136_ = leanh::lean_box(0);
                            leanh::lean_inc(v_declName_3102_);
                            v_tmpDecl_3137_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                            leanh::lean_ctor_set(v_tmpDecl_3137_, 0, v_declName_3102_);
                            leanh::lean_ctor_set(v_tmpDecl_3137_, 1, v___x_3135_);
                            leanh::lean_ctor_set(v_tmpDecl_3137_, 2, v___x_3136_);
                            leanh::lean_ctor_set(v_tmpDecl_3137_, 3, v___x_3103_);
                            v___x_3138_ =
                                l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
                                    v___x_3128_,
                                    v_tmpDecl_3137_,
                                    v___x_3129_,
                                    v___x_3133_,
                                );
                            leanh::lean_dec_ref_known(v_tmpDecl_3137_, 4);
                            leanh::lean_dec_ref(v___x_3128_);
                            if leanh::lean_obj_tag(v___x_3138_) == 0 {
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_3114_);
                                leanh::lean_dec(v_declName_3102_);
                                leanh::lean_dec_ref(v_env_3101_);
                                return v___x_3138_;
                            }
                        }
                    }
                }
            }
            1 => {
                v_toEnvExtension_3107_ = leanh::lean_ctor_get(v___x_3105_, 0);
                v_asyncMode_3108_ = leanh::lean_ctor_get(v_toEnvExtension_3107_, 2);
                v___x_3109_ = leanh::lean_box(0);
                v___x_3110_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_3104_,
                    v___x_3105_,
                    v_env_3101_,
                    v_asyncMode_3108_,
                    v___x_3109_,
                );
                v_snd_3111_ = leanh::lean_ctor_get(v___x_3110_, 1);
                leanh::lean_inc(v_snd_3111_);
                leanh::lean_dec(v___x_3110_);
                v___x_3112_ =
                    l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(
                        v_snd_3111_,
                        v_declName_3102_,
                    );
                leanh::lean_dec(v_declName_3102_);
                leanh::lean_dec(v_snd_3111_);
                return v___x_3112_;
            }
            2 => {
                v___x_3116_ = 0;
                v___x_3117_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_3104_,
                    v___x_3105_,
                    v_env_3101_,
                    v_val_3114_,
                    v___x_3116_,
                );
                leanh::lean_dec(v_val_3114_);
                v___x_3118_ = leanh::lean_unsigned_to_nat(0);
                v___x_3119_ = lean_array_get_size(v___x_3117_);
                v___x_3120_ = lean_nat_dec_lt(v___x_3118_, v___x_3119_);
                if v___x_3120_ == 0 {
                    leanh::lean_dec_ref(v___x_3117_);
                    state = 1;
                    continue;
                } else {
                    v___x_3121_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3122_ = lean_nat_sub(v___x_3119_, v___x_3121_);
                    v___x_3123_ = lean_nat_dec_le(v___x_3118_, v___x_3122_);
                    if v___x_3123_ == 0 {
                        leanh::lean_dec(v___x_3122_);
                        leanh::lean_dec_ref(v___x_3117_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3124_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
                        v___x_3125_ = leanh::lean_box(0);
                        leanh::lean_inc(v_declName_3102_);
                        v_tmpDecl_3126_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v_tmpDecl_3126_, 0, v_declName_3102_);
                        leanh::lean_ctor_set(v_tmpDecl_3126_, 1, v___x_3124_);
                        leanh::lean_ctor_set(v_tmpDecl_3126_, 2, v___x_3125_);
                        leanh::lean_ctor_set(v_tmpDecl_3126_, 3, v___x_3103_);
                        v___x_3127_ =
                            l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
                                v___x_3117_,
                                v_tmpDecl_3126_,
                                v___x_3118_,
                                v___x_3122_,
                            );
                        leanh::lean_dec_ref_known(v_tmpDecl_3126_, 4);
                        leanh::lean_dec_ref(v___x_3117_);
                        if leanh::lean_obj_tag(v___x_3127_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_declName_3102_);
                            leanh::lean_dec_ref(v_env_3101_);
                            return v___x_3127_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(
    mut v_00_u03b2_3139_: *mut leanh::LeanObject,
    mut v_x_3140_: *mut leanh::LeanObject,
    mut v_x_3141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(
        v_x_3140_, v_x_3141_,
    );
    return v___x_3142_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(
    mut v_00_u03b2_3143_: *mut leanh::LeanObject,
    mut v_x_3144_: *mut leanh::LeanObject,
    mut v_x_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(
        v_00_u03b2_3143_,
        v_x_3144_,
        v_x_3145_,
    );
    leanh::lean_dec(v_x_3145_);
    leanh::lean_dec_ref(v_x_3144_);
    return v_res_3146_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(
    mut v_as_3147_: *mut leanh::LeanObject,
    mut v_k_3148_: *mut leanh::LeanObject,
    mut v_x_3149_: *mut leanh::LeanObject,
    mut v_x_3150_: *mut leanh::LeanObject,
    mut v_x_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3152_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
        v_as_3147_, v_k_3148_, v_x_3149_, v_x_3150_,
    );
    return v___x_3152_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(
    mut v_as_3153_: *mut leanh::LeanObject,
    mut v_k_3154_: *mut leanh::LeanObject,
    mut v_x_3155_: *mut leanh::LeanObject,
    mut v_x_3156_: *mut leanh::LeanObject,
    mut v_x_3157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3158_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(
        v_as_3153_, v_k_3154_, v_x_3155_, v_x_3156_, v_x_3157_,
    );
    leanh::lean_dec_ref(v_k_3154_);
    leanh::lean_dec_ref(v_as_3153_);
    return v_res_3158_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(
    mut v_00_u03b2_3159_: *mut leanh::LeanObject,
    mut v_x_3160_: *mut leanh::LeanObject,
    mut v_x_3161_: usize,
    mut v_x_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3163_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_3160_, v_x_3161_, v_x_3162_);
    return v___x_3163_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(
    mut v_00_u03b2_3164_: *mut leanh::LeanObject,
    mut v_x_3165_: *mut leanh::LeanObject,
    mut v_x_3166_: *mut leanh::LeanObject,
    mut v_x_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_585__boxed_3168_: usize = 0;
    let mut v_res_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_585__boxed_3168_ = leanh::lean_unbox_usize(v_x_3166_);
    leanh::lean_dec(v_x_3166_);
    v_res_3169_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_3164_, v_x_3165_, v_x_585__boxed_3168_, v_x_3167_);
    leanh::lean_dec(v_x_3167_);
    leanh::lean_dec_ref(v_x_3165_);
    return v_res_3169_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3170_: *mut leanh::LeanObject,
    mut v_keys_3171_: *mut leanh::LeanObject,
    mut v_vals_3172_: *mut leanh::LeanObject,
    mut v_heq_3173_: *mut leanh::LeanObject,
    mut v_i_3174_: *mut leanh::LeanObject,
    mut v_k_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3176_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_3171_, v_vals_3172_, v_i_3174_, v_k_3175_);
    return v___x_3176_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3177_: *mut leanh::LeanObject,
    mut v_keys_3178_: *mut leanh::LeanObject,
    mut v_vals_3179_: *mut leanh::LeanObject,
    mut v_heq_3180_: *mut leanh::LeanObject,
    mut v_i_3181_: *mut leanh::LeanObject,
    mut v_k_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3183_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_3177_, v_keys_3178_, v_vals_3179_, v_heq_3180_, v_i_3181_, v_k_3182_);
    leanh::lean_dec(v_k_3182_);
    leanh::lean_dec_ref(v_vals_3179_);
    leanh::lean_dec_ref(v_keys_3178_);
    return v_res_3183_;
}
pub unsafe fn lean_ir_find_env_decl(
    mut v_env_3184_: *mut leanh::LeanObject,
    mut v_declName_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: u8 = 0;
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3186_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once), _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
                v___x_3187_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3184_, v_declName_3185_);
                if leanh::lean_obj_tag(v___x_3187_) == 0 {
                    v___x_3188_ = l_Lean_IR_declMapExt;
                    v_toEnvExtension_3189_ = leanh::lean_ctor_get(v___x_3188_, 0);
                    v_asyncMode_3190_ = leanh::lean_ctor_get(v_toEnvExtension_3189_, 2);
                    v___x_3191_ = leanh::lean_box(0);
                    v___x_3192_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_3186_,
                        v___x_3188_,
                        v_env_3184_,
                        v_asyncMode_3190_,
                        v___x_3191_,
                    );
                    v___x_3193_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_3192_, v_declName_3185_);
                    leanh::lean_dec(v_declName_3185_);
                    leanh::lean_dec(v___x_3192_);
                    return v___x_3193_;
                } else {
                    v_val_3194_ = leanh::lean_ctor_get(v___x_3187_, 0);
                    leanh::lean_inc(v_val_3194_);
                    leanh::lean_dec_ref_known(v___x_3187_, 1);
                    v___x_3195_ = leanh::lean_box(0);
                    v___x_3196_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_findEnvDecl___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_IR_findEnvDecl___closed__0_once),
                        _init_l_Lean_IR_findEnvDecl___closed__0,
                    );
                    v___x_3197_ = l_Lean_IR_declMapExt;
                    v___x_3212_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3196_, v___x_3197_, v_env_3184_, v_val_3194_);
                    v___x_3213_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3214_ = lean_array_get_size(v___x_3212_);
                    v___x_3215_ = lean_nat_dec_lt(v___x_3213_, v___x_3214_);
                    if v___x_3215_ == 0 {
                        leanh::lean_dec_ref(v___x_3212_);
                        v___x_3216_ = leanh::lean_box(0);
                        v___y_3199_ = v___x_3216_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3217_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3218_ = lean_nat_sub(v___x_3214_, v___x_3217_);
                        v___x_3219_ = lean_nat_dec_le(v___x_3213_, v___x_3218_);
                        if v___x_3219_ == 0 {
                            leanh::lean_dec(v___x_3218_);
                            leanh::lean_dec_ref(v___x_3212_);
                            v___x_3220_ = leanh::lean_box(0);
                            v___y_3199_ = v___x_3220_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3221_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
                            v___x_3222_ = leanh::lean_box(0);
                            leanh::lean_inc(v_declName_3185_);
                            v_tmpDecl_3223_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                            leanh::lean_ctor_set(v_tmpDecl_3223_, 0, v_declName_3185_);
                            leanh::lean_ctor_set(v_tmpDecl_3223_, 1, v___x_3221_);
                            leanh::lean_ctor_set(v_tmpDecl_3223_, 2, v___x_3222_);
                            leanh::lean_ctor_set(v_tmpDecl_3223_, 3, v___x_3195_);
                            v___x_3224_ =
                                l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
                                    v___x_3212_,
                                    v_tmpDecl_3223_,
                                    v___x_3213_,
                                    v___x_3218_,
                                );
                            leanh::lean_dec_ref_known(v_tmpDecl_3223_, 4);
                            leanh::lean_dec_ref(v___x_3212_);
                            if leanh::lean_obj_tag(v___x_3224_) == 0 {
                                v___y_3199_ = v___x_3224_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_3194_);
                                leanh::lean_dec(v_declName_3185_);
                                leanh::lean_dec_ref(v_env_3184_);
                                return v___x_3224_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3200_ = 0;
                v___x_3201_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_3196_,
                    v___x_3197_,
                    v_env_3184_,
                    v_val_3194_,
                    v___x_3200_,
                );
                leanh::lean_dec(v_val_3194_);
                leanh::lean_dec_ref(v_env_3184_);
                v___x_3202_ = leanh::lean_unsigned_to_nat(0);
                v___x_3203_ = lean_array_get_size(v___x_3201_);
                v___x_3204_ = lean_nat_dec_lt(v___x_3202_, v___x_3203_);
                if v___x_3204_ == 0 {
                    leanh::lean_dec_ref(v___x_3201_);
                    leanh::lean_dec(v_declName_3185_);
                    return v___y_3199_;
                } else {
                    v___x_3205_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3206_ = lean_nat_sub(v___x_3203_, v___x_3205_);
                    v___x_3207_ = lean_nat_dec_le(v___x_3202_, v___x_3206_);
                    if v___x_3207_ == 0 {
                        leanh::lean_dec(v___x_3206_);
                        leanh::lean_dec_ref(v___x_3201_);
                        leanh::lean_dec(v_declName_3185_);
                        return v___y_3199_;
                    } else {
                        leanh::lean_dec(v___y_3199_);
                        v___x_3208_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
                        v___x_3209_ = leanh::lean_box(0);
                        v_tmpDecl_3210_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v_tmpDecl_3210_, 0, v_declName_3185_);
                        leanh::lean_ctor_set(v_tmpDecl_3210_, 1, v___x_3208_);
                        leanh::lean_ctor_set(v_tmpDecl_3210_, 2, v___x_3209_);
                        leanh::lean_ctor_set(v_tmpDecl_3210_, 3, v___x_3195_);
                        v___x_3211_ =
                            l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
                                v___x_3201_,
                                v_tmpDecl_3210_,
                                v___x_3202_,
                                v___x_3206_,
                            );
                        leanh::lean_dec_ref_known(v_tmpDecl_3210_, 4);
                        leanh::lean_dec_ref(v___x_3201_);
                        return v___x_3211_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_ir_find_env_decl_boxed(
    mut v_env_3225_: *mut leanh::LeanObject,
    mut v_declName_3226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_boxed_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: u8 = 0;
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: u8 = 0;
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once), _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
                leanh::lean_inc(v_declName_3226_);
                v_boxed_3228_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_3226_);
                v___x_3229_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3225_, v_declName_3226_);
                leanh::lean_dec(v_declName_3226_);
                if leanh::lean_obj_tag(v___x_3229_) == 0 {
                    v___x_3230_ = l_Lean_IR_declMapExt;
                    v_toEnvExtension_3231_ = leanh::lean_ctor_get(v___x_3230_, 0);
                    v_asyncMode_3232_ = leanh::lean_ctor_get(v_toEnvExtension_3231_, 2);
                    v___x_3233_ = leanh::lean_box(0);
                    v___x_3234_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_3227_,
                        v___x_3230_,
                        v_env_3225_,
                        v_asyncMode_3232_,
                        v___x_3233_,
                    );
                    v___x_3235_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_3234_, v_boxed_3228_);
                    leanh::lean_dec(v_boxed_3228_);
                    leanh::lean_dec(v___x_3234_);
                    return v___x_3235_;
                } else {
                    v_val_3236_ = leanh::lean_ctor_get(v___x_3229_, 0);
                    leanh::lean_inc(v_val_3236_);
                    leanh::lean_dec_ref_known(v___x_3229_, 1);
                    v___x_3237_ = leanh::lean_box(0);
                    v___x_3238_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_findEnvDecl___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_IR_findEnvDecl___closed__0_once),
                        _init_l_Lean_IR_findEnvDecl___closed__0,
                    );
                    v___x_3239_ = l_Lean_IR_declMapExt;
                    v___x_3254_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3238_, v___x_3239_, v_env_3225_, v_val_3236_);
                    v___x_3255_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3256_ = lean_array_get_size(v___x_3254_);
                    v___x_3257_ = lean_nat_dec_lt(v___x_3255_, v___x_3256_);
                    if v___x_3257_ == 0 {
                        leanh::lean_dec_ref(v___x_3254_);
                        v___x_3258_ = leanh::lean_box(0);
                        v___y_3241_ = v___x_3258_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3259_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3260_ = lean_nat_sub(v___x_3256_, v___x_3259_);
                        v___x_3261_ = lean_nat_dec_le(v___x_3255_, v___x_3260_);
                        if v___x_3261_ == 0 {
                            leanh::lean_dec(v___x_3260_);
                            leanh::lean_dec_ref(v___x_3254_);
                            v___x_3262_ = leanh::lean_box(0);
                            v___y_3241_ = v___x_3262_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3263_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
                            v___x_3264_ = leanh::lean_box(0);
                            leanh::lean_inc(v_boxed_3228_);
                            v_tmpDecl_3265_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                            leanh::lean_ctor_set(v_tmpDecl_3265_, 0, v_boxed_3228_);
                            leanh::lean_ctor_set(v_tmpDecl_3265_, 1, v___x_3263_);
                            leanh::lean_ctor_set(v_tmpDecl_3265_, 2, v___x_3264_);
                            leanh::lean_ctor_set(v_tmpDecl_3265_, 3, v___x_3237_);
                            v___x_3266_ =
                                l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
                                    v___x_3254_,
                                    v_tmpDecl_3265_,
                                    v___x_3255_,
                                    v___x_3260_,
                                );
                            leanh::lean_dec_ref_known(v_tmpDecl_3265_, 4);
                            leanh::lean_dec_ref(v___x_3254_);
                            if leanh::lean_obj_tag(v___x_3266_) == 0 {
                                v___y_3241_ = v___x_3266_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_3236_);
                                leanh::lean_dec(v_boxed_3228_);
                                leanh::lean_dec_ref(v_env_3225_);
                                return v___x_3266_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3242_ = 0;
                v___x_3243_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_3238_,
                    v___x_3239_,
                    v_env_3225_,
                    v_val_3236_,
                    v___x_3242_,
                );
                leanh::lean_dec(v_val_3236_);
                leanh::lean_dec_ref(v_env_3225_);
                v___x_3244_ = leanh::lean_unsigned_to_nat(0);
                v___x_3245_ = lean_array_get_size(v___x_3243_);
                v___x_3246_ = lean_nat_dec_lt(v___x_3244_, v___x_3245_);
                if v___x_3246_ == 0 {
                    leanh::lean_dec_ref(v___x_3243_);
                    leanh::lean_dec(v_boxed_3228_);
                    return v___y_3241_;
                } else {
                    v___x_3247_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3248_ = lean_nat_sub(v___x_3245_, v___x_3247_);
                    v___x_3249_ = lean_nat_dec_le(v___x_3244_, v___x_3248_);
                    if v___x_3249_ == 0 {
                        leanh::lean_dec(v___x_3248_);
                        leanh::lean_dec_ref(v___x_3243_);
                        leanh::lean_dec(v_boxed_3228_);
                        return v___y_3241_;
                    } else {
                        leanh::lean_dec(v___y_3241_);
                        v___x_3250_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
                        v___x_3251_ = leanh::lean_box(0);
                        v_tmpDecl_3252_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v_tmpDecl_3252_, 0, v_boxed_3228_);
                        leanh::lean_ctor_set(v_tmpDecl_3252_, 1, v___x_3250_);
                        leanh::lean_ctor_set(v_tmpDecl_3252_, 2, v___x_3251_);
                        leanh::lean_ctor_set(v_tmpDecl_3252_, 3, v___x_3237_);
                        v___x_3253_ =
                            l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(
                                v___x_3243_,
                                v_tmpDecl_3252_,
                                v___x_3244_,
                                v___x_3248_,
                            );
                        leanh::lean_dec_ref_known(v_tmpDecl_3252_, 4);
                        leanh::lean_dec_ref(v___x_3243_);
                        return v___x_3253_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_has_compile_error(
    mut v_env_3267_: *mut leanh::LeanObject,
    mut v_constName_3268_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3269_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3267_, v_constName_3268_);
    if leanh::lean_obj_tag(v___x_3269_) == 0 {
        let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toEnvExtension_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3276_: u8 = 0;
        v___x_3270_ = l_Lean_IR_declMapExt;
        v_toEnvExtension_3271_ = leanh::lean_ctor_get(v___x_3270_, 0);
        v_asyncMode_3272_ = leanh::lean_ctor_get(v_toEnvExtension_3271_, 2);
        v___x_3273_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once
            ),
            _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2,
        );
        v___x_3274_ = leanh::lean_box(0);
        v___x_3275_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
            v___x_3273_,
            v___x_3270_,
            v_env_3267_,
            v_asyncMode_3272_,
            v___x_3274_,
        );
        v___x_3276_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2__spec__3___redArg(v___x_3275_, v_constName_3268_);
        leanh::lean_dec(v_constName_3268_);
        leanh::lean_dec(v___x_3275_);
        if v___x_3276_ == 0 {
            let mut v___x_3277_: u8 = 0;
            v___x_3277_ = 1;
            return v___x_3277_;
        } else {
            let mut v___x_3278_: u8 = 0;
            v___x_3278_ = 0;
            return v___x_3278_;
        }
    } else {
        let mut v___x_3279_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_3269_, 1);
        leanh::lean_dec(v_constName_3268_);
        leanh::lean_dec_ref(v_env_3267_);
        v___x_3279_ = 0;
        return v___x_3279_;
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(
    mut v_env_3280_: *mut leanh::LeanObject,
    mut v_constName_3281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3282_: u8 = 0;
    let mut v_r_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3282_ = lean_has_compile_error(v_env_3280_, v_constName_3281_);
    v_r_3283_ = leanh::lean_box((v_res_3282_) as usize);
    return v_r_3283_;
}
pub unsafe fn l_Lean_IR_findDecl___redArg(
    mut v_n_3284_: *mut leanh::LeanObject,
    mut v_a_3285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3287_ = lean_st_ref_get(v_a_3285_);
    v_env_3288_ = leanh::lean_ctor_get(v___x_3287_, 0);
    leanh::lean_inc_ref(v_env_3288_);
    leanh::lean_dec(v___x_3287_);
    v___x_3289_ = l_Lean_IR_findEnvDecl(v_env_3288_, v_n_3284_);
    v___x_3290_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3290_, 0, v___x_3289_);
    return v___x_3290_;
}
pub unsafe fn l_Lean_IR_findDecl___redArg___boxed(
    mut v_n_3291_: *mut leanh::LeanObject,
    mut v_a_3292_: *mut leanh::LeanObject,
    mut v_a_3293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3294_ = l_Lean_IR_findDecl___redArg(v_n_3291_, v_a_3292_);
    leanh::lean_dec(v_a_3292_);
    return v_res_3294_;
}
pub unsafe fn l_Lean_IR_findDecl(
    mut v_n_3295_: *mut leanh::LeanObject,
    mut v_a_3296_: *mut leanh::LeanObject,
    mut v_a_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3299_ = l_Lean_IR_findDecl___redArg(v_n_3295_, v_a_3297_);
    return v___x_3299_;
}
pub unsafe fn l_Lean_IR_findDecl___boxed(
    mut v_n_3300_: *mut leanh::LeanObject,
    mut v_a_3301_: *mut leanh::LeanObject,
    mut v_a_3302_: *mut leanh::LeanObject,
    mut v_a_3303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3304_ = l_Lean_IR_findDecl(v_n_3300_, v_a_3301_, v_a_3302_);
    leanh::lean_dec(v_a_3302_);
    leanh::lean_dec_ref(v_a_3301_);
    return v_res_3304_;
}
pub unsafe fn l_Lean_IR_containsDecl___redArg(
    mut v_n_3305_: *mut leanh::LeanObject,
    mut v_a_3306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v___x_3313_: u8 = 0;
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3308_ = l_Lean_IR_findDecl___redArg(v_n_3305_, v_a_3306_);
                v_a_3309_ = leanh::lean_ctor_get(v___x_3308_, 0);
                v_isSharedCheck_3323_ = (!leanh::lean_is_exclusive(v___x_3308_)) as u8;
                if v_isSharedCheck_3323_ == 0 {
                    v___x_3311_ = v___x_3308_;
                    v_isShared_3312_ = v_isSharedCheck_3323_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3309_);
                    leanh::lean_dec(v___x_3308_);
                    v___x_3311_ = leanh::lean_box(0);
                    v_isShared_3312_ = v_isSharedCheck_3323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3309_) == 0 {
                    v___x_3313_ = 0;
                    v___x_3314_ = leanh::lean_box((v___x_3313_) as usize);
                    if v_isShared_3312_ == 0 {
                        leanh::lean_ctor_set(v___x_3311_, 0, v___x_3314_);
                        v___x_3316_ = v___x_3311_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3317_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
                        v___x_3316_ = v_reuseFailAlloc_3317_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_3309_, 1);
                    v___x_3318_ = 1;
                    v___x_3319_ = leanh::lean_box((v___x_3318_) as usize);
                    if v_isShared_3312_ == 0 {
                        leanh::lean_ctor_set(v___x_3311_, 0, v___x_3319_);
                        v___x_3321_ = v___x_3311_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
                        v___x_3321_ = v_reuseFailAlloc_3322_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3316_;
            }
            3 => {
                return v___x_3321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_containsDecl___redArg___boxed(
    mut v_n_3324_: *mut leanh::LeanObject,
    mut v_a_3325_: *mut leanh::LeanObject,
    mut v_a_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Lean_IR_containsDecl___redArg(v_n_3324_, v_a_3325_);
    leanh::lean_dec(v_a_3325_);
    return v_res_3327_;
}
pub unsafe fn l_Lean_IR_containsDecl(
    mut v_n_3328_: *mut leanh::LeanObject,
    mut v_a_3329_: *mut leanh::LeanObject,
    mut v_a_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3332_ = l_Lean_IR_containsDecl___redArg(v_n_3328_, v_a_3330_);
    return v___x_3332_;
}
pub unsafe fn l_Lean_IR_containsDecl___boxed(
    mut v_n_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Lean_IR_containsDecl(v_n_3333_, v_a_3334_, v_a_3335_);
    leanh::lean_dec(v_a_3335_);
    leanh::lean_dec_ref(v_a_3334_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(
    mut v_msg_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3347_: u8 = 0;
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3342_ = leanh::lean_ctor_get(v___y_3339_, 5);
                v___x_3343_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_3338_, v___y_3339_, v___y_3340_);
                v_a_3344_ = leanh::lean_ctor_get(v___x_3343_, 0);
                v_isSharedCheck_3352_ = (!leanh::lean_is_exclusive(v___x_3343_)) as u8;
                if v_isSharedCheck_3352_ == 0 {
                    v___x_3346_ = v___x_3343_;
                    v_isShared_3347_ = v_isSharedCheck_3352_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3344_);
                    leanh::lean_dec(v___x_3343_);
                    v___x_3346_ = leanh::lean_box(0);
                    v_isShared_3347_ = v_isSharedCheck_3352_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3342_);
                v___x_3348_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3348_, 0, v_ref_3342_);
                leanh::lean_ctor_set(v___x_3348_, 1, v_a_3344_);
                if v_isShared_3347_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3346_, 1);
                    leanh::lean_ctor_set(v___x_3346_, 0, v___x_3348_);
                    v___x_3350_ = v___x_3346_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
                    v___x_3350_ = v_reuseFailAlloc_3351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(
    mut v_msg_3353_: *mut leanh::LeanObject,
    mut v___y_3354_: *mut leanh::LeanObject,
    mut v___y_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(
        v_msg_3353_,
        v___y_3354_,
        v___y_3355_,
    );
    leanh::lean_dec(v___y_3355_);
    leanh::lean_dec_ref(v___y_3354_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_IR_getDecl(
    mut v_n_3360_: *mut leanh::LeanObject,
    mut v_a_3361_: *mut leanh::LeanObject,
    mut v_a_3362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v_val_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_n_3360_);
                v___x_3364_ = l_Lean_IR_findDecl___redArg(v_n_3360_, v_a_3362_);
                v_a_3365_ = leanh::lean_ctor_get(v___x_3364_, 0);
                v_isSharedCheck_3382_ = (!leanh::lean_is_exclusive(v___x_3364_)) as u8;
                if v_isSharedCheck_3382_ == 0 {
                    v___x_3367_ = v___x_3364_;
                    v_isShared_3368_ = v_isSharedCheck_3382_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3365_);
                    leanh::lean_dec(v___x_3364_);
                    v___x_3367_ = leanh::lean_box(0);
                    v_isShared_3368_ = v_isSharedCheck_3382_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3365_) == 1 {
                    leanh::lean_dec(v_n_3360_);
                    v_val_3369_ = leanh::lean_ctor_get(v_a_3365_, 0);
                    leanh::lean_inc(v_val_3369_);
                    leanh::lean_dec_ref_known(v_a_3365_, 1);
                    if v_isShared_3368_ == 0 {
                        leanh::lean_ctor_set(v___x_3367_, 0, v_val_3369_);
                        v___x_3371_ = v___x_3367_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3372_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_val_3369_);
                        v___x_3371_ = v_reuseFailAlloc_3372_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3367_);
                    leanh::lean_dec(v_a_3365_);
                    v___x_3373_ = l_Lean_IR_getDecl___closed__0;
                    v___x_3374_ = 1;
                    v___x_3375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_n_3360_,
                        v___x_3374_,
                    );
                    v___x_3376_ = lean_string_append(v___x_3373_, v___x_3375_);
                    leanh::lean_dec_ref(v___x_3375_);
                    v___x_3377_ = l_Lean_IR_getDecl___closed__1;
                    v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
                    v___x_3379_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3379_, 0, v___x_3378_);
                    v___x_3380_ = l_Lean_MessageData_ofFormat(v___x_3379_);
                    v___x_3381_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(
                        v___x_3380_,
                        v_a_3361_,
                        v_a_3362_,
                    );
                    return v___x_3381_;
                }
            }
            2 => {
                return v___x_3371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_getDecl___boxed(
    mut v_n_3383_: *mut leanh::LeanObject,
    mut v_a_3384_: *mut leanh::LeanObject,
    mut v_a_3385_: *mut leanh::LeanObject,
    mut v_a_3386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_Lean_IR_getDecl(v_n_3383_, v_a_3384_, v_a_3385_);
    leanh::lean_dec(v_a_3385_);
    leanh::lean_dec_ref(v_a_3384_);
    return v_res_3387_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(
    mut v_00_u03b1_3388_: *mut leanh::LeanObject,
    mut v_msg_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(
        v_msg_3389_,
        v___y_3390_,
        v___y_3391_,
    );
    return v___x_3393_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(
    mut v_00_u03b1_3394_: *mut leanh::LeanObject,
    mut v_msg_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3399_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(
        v_00_u03b1_3394_,
        v_msg_3395_,
        v___y_3396_,
        v___y_3397_,
    );
    leanh::lean_dec(v___y_3397_);
    leanh::lean_dec_ref(v___y_3396_);
    return v_res_3399_;
}
pub unsafe fn l_Lean_IR_findLocalDecl___redArg(
    mut v_n_3400_: *mut leanh::LeanObject,
    mut v_a_3401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = lean_st_ref_get(v_a_3401_);
    v_env_3404_ = leanh::lean_ctor_get(v___x_3403_, 0);
    leanh::lean_inc_ref(v_env_3404_);
    leanh::lean_dec(v___x_3403_);
    v___x_3405_ = l_Lean_IR_declMapExt;
    v_toEnvExtension_3406_ = leanh::lean_ctor_get(v___x_3405_, 0);
    v_asyncMode_3407_ = leanh::lean_ctor_get(v_toEnvExtension_3406_, 2);
    v___x_3408_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once
        ),
        _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2,
    );
    v___x_3409_ = leanh::lean_box(0);
    v___x_3410_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_3408_,
        v___x_3405_,
        v_env_3404_,
        v_asyncMode_3407_,
        v___x_3409_,
    );
    v___x_3411_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(
        v___x_3410_,
        v_n_3400_,
    );
    leanh::lean_dec(v___x_3410_);
    v___x_3412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3412_, 0, v___x_3411_);
    return v___x_3412_;
}
pub unsafe fn l_Lean_IR_findLocalDecl___redArg___boxed(
    mut v_n_3413_: *mut leanh::LeanObject,
    mut v_a_3414_: *mut leanh::LeanObject,
    mut v_a_3415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_Lean_IR_findLocalDecl___redArg(v_n_3413_, v_a_3414_);
    leanh::lean_dec(v_a_3414_);
    leanh::lean_dec(v_n_3413_);
    return v_res_3416_;
}
pub unsafe fn l_Lean_IR_findLocalDecl(
    mut v_n_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = l_Lean_IR_findLocalDecl___redArg(v_n_3417_, v_a_3419_);
    return v___x_3421_;
}
pub unsafe fn l_Lean_IR_findLocalDecl___boxed(
    mut v_n_3422_: *mut leanh::LeanObject,
    mut v_a_3423_: *mut leanh::LeanObject,
    mut v_a_3424_: *mut leanh::LeanObject,
    mut v_a_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ = l_Lean_IR_findLocalDecl(v_n_3422_, v_a_3423_, v_a_3424_);
    leanh::lean_dec(v_a_3424_);
    leanh::lean_dec_ref(v_a_3423_);
    leanh::lean_dec(v_n_3422_);
    return v_res_3426_;
}
pub unsafe fn l_Lean_IR_getDecls(
    mut v_env_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3428_ = l_Lean_IR_declMapExt;
    v_toEnvExtension_3429_ = leanh::lean_ctor_get(v___x_3428_, 0);
    v_asyncMode_3430_ = leanh::lean_ctor_get(v_toEnvExtension_3429_, 2);
    v___x_3431_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once
        ),
        _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2,
    );
    v___x_3432_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v___x_3431_,
        v___x_3428_,
        v_env_3427_,
        v_asyncMode_3430_,
    );
    return v___x_3432_;
}
pub unsafe fn _init_l_Lean_IR_addDecl___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3433_;
}
pub unsafe fn _init_l_Lean_IR_addDecl___redArg___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_addDecl___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_addDecl___redArg___closed__0_once),
        _init_l_Lean_IR_addDecl___redArg___closed__0,
    );
    v___x_3435_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3435_, 0, v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn _init_l_Lean_IR_addDecl___redArg___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3436_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_addDecl___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_addDecl___redArg___closed__1_once),
        _init_l_Lean_IR_addDecl___redArg___closed__1,
    );
    v___x_3437_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3437_, 0, v___x_3436_);
    leanh::lean_ctor_set(v___x_3437_, 1, v___x_3436_);
    return v___x_3437_;
}
pub unsafe fn l_Lean_IR_addDecl___redArg(
    mut v_decl_3438_: *mut leanh::LeanObject,
    mut v_a_3439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_unused_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3441_ = lean_st_ref_take(v_a_3439_);
                v_env_3442_ = leanh::lean_ctor_get(v___x_3441_, 0);
                v_nextMacroScope_3443_ = leanh::lean_ctor_get(v___x_3441_, 1);
                v_ngen_3444_ = leanh::lean_ctor_get(v___x_3441_, 2);
                v_auxDeclNGen_3445_ = leanh::lean_ctor_get(v___x_3441_, 3);
                v_traceState_3446_ = leanh::lean_ctor_get(v___x_3441_, 4);
                v_messages_3447_ = leanh::lean_ctor_get(v___x_3441_, 6);
                v_infoState_3448_ = leanh::lean_ctor_get(v___x_3441_, 7);
                v_snapshotTasks_3449_ = leanh::lean_ctor_get(v___x_3441_, 8);
                v_isSharedCheck_3465_ = (!leanh::lean_is_exclusive(v___x_3441_)) as u8;
                if v_isSharedCheck_3465_ == 0 {
                    v_unused_3466_ = leanh::lean_ctor_get(v___x_3441_, 5);
                    leanh::lean_dec(v_unused_3466_);
                    v___x_3451_ = v___x_3441_;
                    v_isShared_3452_ = v_isSharedCheck_3465_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3449_);
                    leanh::lean_inc(v_infoState_3448_);
                    leanh::lean_inc(v_messages_3447_);
                    leanh::lean_inc(v_traceState_3446_);
                    leanh::lean_inc(v_auxDeclNGen_3445_);
                    leanh::lean_inc(v_ngen_3444_);
                    leanh::lean_inc(v_nextMacroScope_3443_);
                    leanh::lean_inc(v_env_3442_);
                    leanh::lean_dec(v___x_3441_);
                    v___x_3451_ = leanh::lean_box(0);
                    v_isShared_3452_ = v_isSharedCheck_3465_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3453_ = l_Lean_IR_declMapExt;
                v_toEnvExtension_3454_ = leanh::lean_ctor_get(v___x_3453_, 0);
                v_asyncMode_3455_ = leanh::lean_ctor_get(v_toEnvExtension_3454_, 2);
                v___x_3456_ = leanh::lean_box(0);
                v___x_3457_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3453_,
                    v_env_3442_,
                    v_decl_3438_,
                    v_asyncMode_3455_,
                    v___x_3456_,
                );
                v___x_3458_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_addDecl___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_IR_addDecl___redArg___closed__2_once),
                    _init_l_Lean_IR_addDecl___redArg___closed__2,
                );
                if v_isShared_3452_ == 0 {
                    leanh::lean_ctor_set(v___x_3451_, 5, v___x_3458_);
                    leanh::lean_ctor_set(v___x_3451_, 0, v___x_3457_);
                    v___x_3460_ = v___x_3451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3457_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_nextMacroScope_3443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_ngen_3444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 3, v_auxDeclNGen_3445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 4, v_traceState_3446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 5, v___x_3458_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 6, v_messages_3447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 7, v_infoState_3448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 8, v_snapshotTasks_3449_);
                    v___x_3460_ = v_reuseFailAlloc_3464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3461_ = lean_st_ref_set(v_a_3439_, v___x_3460_);
                v___x_3462_ = leanh::lean_box(0);
                v___x_3463_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3463_, 0, v___x_3462_);
                return v___x_3463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_addDecl___redArg___boxed(
    mut v_decl_3467_: *mut leanh::LeanObject,
    mut v_a_3468_: *mut leanh::LeanObject,
    mut v_a_3469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3470_ = l_Lean_IR_addDecl___redArg(v_decl_3467_, v_a_3468_);
    leanh::lean_dec(v_a_3468_);
    return v_res_3470_;
}
pub unsafe fn l_Lean_IR_addDecl(
    mut v_decl_3471_: *mut leanh::LeanObject,
    mut v_a_3472_: *mut leanh::LeanObject,
    mut v_a_3473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ = l_Lean_IR_addDecl___redArg(v_decl_3471_, v_a_3473_);
    return v___x_3475_;
}
pub unsafe fn l_Lean_IR_addDecl___boxed(
    mut v_decl_3476_: *mut leanh::LeanObject,
    mut v_a_3477_: *mut leanh::LeanObject,
    mut v_a_3478_: *mut leanh::LeanObject,
    mut v_a_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Lean_IR_addDecl(v_decl_3476_, v_a_3477_, v_a_3478_);
    leanh::lean_dec(v_a_3478_);
    leanh::lean_dec_ref(v_a_3477_);
    return v_res_3480_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(
    mut v_as_3481_: *mut leanh::LeanObject,
    mut v_i_3482_: usize,
    mut v_stop_3483_: usize,
    mut v_b_3484_: *mut leanh::LeanObject,
    mut v___y_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3487_: u8 = 0;
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: usize = 0;
    let mut v___x_3492_: usize = 0;
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3487_ = lean_usize_dec_eq(v_i_3482_, v_stop_3483_);
                if v___x_3487_ == 0 {
                    v___x_3488_ = lean_array_uget_borrowed(v_as_3481_, v_i_3482_);
                    leanh::lean_inc(v___x_3488_);
                    v___x_3489_ = l_Lean_IR_addDecl___redArg(v___x_3488_, v___y_3485_);
                    if leanh::lean_obj_tag(v___x_3489_) == 0 {
                        v_a_3490_ = leanh::lean_ctor_get(v___x_3489_, 0);
                        leanh::lean_inc(v_a_3490_);
                        leanh::lean_dec_ref_known(v___x_3489_, 1);
                        v___x_3491_ = 1usize;
                        v___x_3492_ = lean_usize_add(v_i_3482_, v___x_3491_);
                        v_i_3482_ = v___x_3492_;
                        v_b_3484_ = v_a_3490_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3489_;
                    }
                } else {
                    v___x_3494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3494_, 0, v_b_3484_);
                    return v___x_3494_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(
    mut v_as_3495_: *mut leanh::LeanObject,
    mut v_i_3496_: *mut leanh::LeanObject,
    mut v_stop_3497_: *mut leanh::LeanObject,
    mut v_b_3498_: *mut leanh::LeanObject,
    mut v___y_3499_: *mut leanh::LeanObject,
    mut v___y_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3501_: usize = 0;
    let mut v_stop_boxed_3502_: usize = 0;
    let mut v_res_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3501_ = leanh::lean_unbox_usize(v_i_3496_);
    leanh::lean_dec(v_i_3496_);
    v_stop_boxed_3502_ = leanh::lean_unbox_usize(v_stop_3497_);
    leanh::lean_dec(v_stop_3497_);
    v_res_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_3495_, v_i_boxed_3501_, v_stop_boxed_3502_, v_b_3498_, v___y_3499_);
    leanh::lean_dec(v___y_3499_);
    leanh::lean_dec_ref(v_as_3495_);
    return v_res_3503_;
}
pub unsafe fn l_Lean_IR_addDecls(
    mut v_decls_3504_: *mut leanh::LeanObject,
    mut v_a_3505_: *mut leanh::LeanObject,
    mut v_a_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    v___x_3508_ = leanh::lean_unsigned_to_nat(0);
    v___x_3509_ = lean_array_get_size(v_decls_3504_);
    v___x_3510_ = leanh::lean_box(0);
    v___x_3511_ = lean_nat_dec_lt(v___x_3508_, v___x_3509_);
    if v___x_3511_ == 0 {
        let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3512_, 0, v___x_3510_);
        return v___x_3512_;
    } else {
        let mut v___x_3513_: u8 = 0;
        v___x_3513_ = lean_nat_dec_le(v___x_3509_, v___x_3509_);
        if v___x_3513_ == 0 {
            if v___x_3511_ == 0 {
                let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3514_, 0, v___x_3510_);
                return v___x_3514_;
            } else {
                let mut v___x_3515_: usize = 0;
                let mut v___x_3516_: usize = 0;
                let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3515_ = 0usize;
                v___x_3516_ = lean_usize_of_nat(v___x_3509_);
                v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_3504_, v___x_3515_, v___x_3516_, v___x_3510_, v_a_3506_);
                return v___x_3517_;
            }
        } else {
            let mut v___x_3518_: usize = 0;
            let mut v___x_3519_: usize = 0;
            let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3518_ = 0usize;
            v___x_3519_ = lean_usize_of_nat(v___x_3509_);
            v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_3504_, v___x_3518_, v___x_3519_, v___x_3510_, v_a_3506_);
            return v___x_3520_;
        }
    }
}
pub unsafe fn l_Lean_IR_addDecls___boxed(
    mut v_decls_3521_: *mut leanh::LeanObject,
    mut v_a_3522_: *mut leanh::LeanObject,
    mut v_a_3523_: *mut leanh::LeanObject,
    mut v_a_3524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3525_ = l_Lean_IR_addDecls(v_decls_3521_, v_a_3522_, v_a_3523_);
    leanh::lean_dec(v_a_3523_);
    leanh::lean_dec_ref(v_a_3522_);
    leanh::lean_dec_ref(v_decls_3521_);
    return v_res_3525_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(
    mut v_as_3526_: *mut leanh::LeanObject,
    mut v_i_3527_: usize,
    mut v_stop_3528_: usize,
    mut v_b_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
    mut v___y_3531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_3526_, v_i_3527_, v_stop_3528_, v_b_3529_, v___y_3531_);
    return v___x_3533_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(
    mut v_as_3534_: *mut leanh::LeanObject,
    mut v_i_3535_: *mut leanh::LeanObject,
    mut v_stop_3536_: *mut leanh::LeanObject,
    mut v_b_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
    mut v___y_3539_: *mut leanh::LeanObject,
    mut v___y_3540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3541_: usize = 0;
    let mut v_stop_boxed_3542_: usize = 0;
    let mut v_res_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3541_ = leanh::lean_unbox_usize(v_i_3535_);
    leanh::lean_dec(v_i_3535_);
    v_stop_boxed_3542_ = leanh::lean_unbox_usize(v_stop_3536_);
    leanh::lean_dec(v_stop_3536_);
    v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_3534_, v_i_boxed_3541_, v_stop_boxed_3542_, v_b_3537_, v___y_3538_, v___y_3539_);
    leanh::lean_dec(v___y_3539_);
    leanh::lean_dec_ref(v___y_3538_);
    leanh::lean_dec_ref(v_as_3534_);
    return v_res_3543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(
    mut v_n_3547_: *mut leanh::LeanObject,
    mut v_as_3548_: *mut leanh::LeanObject,
    mut v_sz_3549_: usize,
    mut v_i_3550_: usize,
    mut v_b_3551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3552_: u8 = 0;
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: usize = 0;
    let mut v___x_3559_: usize = 0;
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3552_ = lean_usize_dec_lt(v_i_3550_, v_sz_3549_);
                if v___x_3552_ == 0 {
                    leanh::lean_inc_ref(v_b_3551_);
                    return v_b_3551_;
                } else {
                    v___x_3553_ = leanh::lean_box(0);
                    v_a_3554_ = lean_array_uget_borrowed(v_as_3548_, v_i_3550_);
                    v___x_3555_ = l_Lean_IR_Decl_name(v_a_3554_);
                    v___x_3556_ = lean_name_eq(v___x_3555_, v_n_3547_);
                    leanh::lean_dec(v___x_3555_);
                    if v___x_3556_ == 0 {
                        v___x_3557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0;
                        v___x_3558_ = 1usize;
                        v___x_3559_ = lean_usize_add(v_i_3550_, v___x_3558_);
                        v_i_3550_ = v___x_3559_;
                        v_b_3551_ = v___x_3557_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3554_);
                        v___x_3561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3561_, 0, v_a_3554_);
                        v___x_3562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3562_, 0, v___x_3561_);
                        v___x_3563_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3563_, 0, v___x_3562_);
                        leanh::lean_ctor_set(v___x_3563_, 1, v___x_3553_);
                        return v___x_3563_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(
    mut v_n_3564_: *mut leanh::LeanObject,
    mut v_as_3565_: *mut leanh::LeanObject,
    mut v_sz_3566_: *mut leanh::LeanObject,
    mut v_i_3567_: *mut leanh::LeanObject,
    mut v_b_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3569_: usize = 0;
    let mut v_i_boxed_3570_: usize = 0;
    let mut v_res_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3569_ = leanh::lean_unbox_usize(v_sz_3566_);
    leanh::lean_dec(v_sz_3566_);
    v_i_boxed_3570_ = leanh::lean_unbox_usize(v_i_3567_);
    leanh::lean_dec(v_i_3567_);
    v_res_3571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_3564_, v_as_3565_, v_sz_boxed_3569_, v_i_boxed_3570_, v_b_3568_);
    leanh::lean_dec_ref(v_b_3568_);
    leanh::lean_dec_ref(v_as_3565_);
    leanh::lean_dec(v_n_3564_);
    return v_res_3571_;
}
pub unsafe fn l_Lean_IR_findEnvDecl_x27(
    mut v_env_3572_: *mut leanh::LeanObject,
    mut v_n_3573_: *mut leanh::LeanObject,
    mut v_decls_3574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3576_: usize = 0;
    let mut v___x_3577_: usize = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0;
    v_sz_3576_ = lean_array_size(v_decls_3574_);
    v___x_3577_ = 0usize;
    v___x_3578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_3573_, v_decls_3574_, v_sz_3576_, v___x_3577_, v___x_3575_);
    v_fst_3579_ = leanh::lean_ctor_get(v___x_3578_, 0);
    leanh::lean_inc(v_fst_3579_);
    leanh::lean_dec_ref(v___x_3578_);
    if leanh::lean_obj_tag(v_fst_3579_) == 0 {
        let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3580_ = l_Lean_IR_findEnvDecl(v_env_3572_, v_n_3573_);
        return v___x_3580_;
    } else {
        let mut v_val_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3581_ = leanh::lean_ctor_get(v_fst_3579_, 0);
        leanh::lean_inc(v_val_3581_);
        leanh::lean_dec_ref_known(v_fst_3579_, 1);
        if leanh::lean_obj_tag(v_val_3581_) == 0 {
            let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3582_ = l_Lean_IR_findEnvDecl(v_env_3572_, v_n_3573_);
            return v___x_3582_;
        } else {
            leanh::lean_dec(v_n_3573_);
            leanh::lean_dec_ref(v_env_3572_);
            return v_val_3581_;
        }
    }
}
pub unsafe fn l_Lean_IR_findEnvDecl_x27___boxed(
    mut v_env_3583_: *mut leanh::LeanObject,
    mut v_n_3584_: *mut leanh::LeanObject,
    mut v_decls_3585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3586_ = l_Lean_IR_findEnvDecl_x27(v_env_3583_, v_n_3584_, v_decls_3585_);
    leanh::lean_dec_ref(v_decls_3585_);
    return v_res_3586_;
}
pub unsafe fn l_Lean_IR_findDecl_x27___redArg(
    mut v_n_3587_: *mut leanh::LeanObject,
    mut v_decls_3588_: *mut leanh::LeanObject,
    mut v_a_3589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3591_ = lean_st_ref_get(v_a_3589_);
    v_env_3592_ = leanh::lean_ctor_get(v___x_3591_, 0);
    leanh::lean_inc_ref(v_env_3592_);
    leanh::lean_dec(v___x_3591_);
    v___x_3593_ = l_Lean_IR_findEnvDecl_x27(v_env_3592_, v_n_3587_, v_decls_3588_);
    v___x_3594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3594_, 0, v___x_3593_);
    return v___x_3594_;
}
pub unsafe fn l_Lean_IR_findDecl_x27___redArg___boxed(
    mut v_n_3595_: *mut leanh::LeanObject,
    mut v_decls_3596_: *mut leanh::LeanObject,
    mut v_a_3597_: *mut leanh::LeanObject,
    mut v_a_3598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Lean_IR_findDecl_x27___redArg(v_n_3595_, v_decls_3596_, v_a_3597_);
    leanh::lean_dec(v_a_3597_);
    leanh::lean_dec_ref(v_decls_3596_);
    return v_res_3599_;
}
pub unsafe fn l_Lean_IR_findDecl_x27(
    mut v_n_3600_: *mut leanh::LeanObject,
    mut v_decls_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v_a_3603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3605_ = l_Lean_IR_findDecl_x27___redArg(v_n_3600_, v_decls_3601_, v_a_3603_);
    return v___x_3605_;
}
pub unsafe fn l_Lean_IR_findDecl_x27___boxed(
    mut v_n_3606_: *mut leanh::LeanObject,
    mut v_decls_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
    mut v_a_3609_: *mut leanh::LeanObject,
    mut v_a_3610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3611_ = l_Lean_IR_findDecl_x27(v_n_3606_, v_decls_3607_, v_a_3608_, v_a_3609_);
    leanh::lean_dec(v_a_3609_);
    leanh::lean_dec_ref(v_a_3608_);
    leanh::lean_dec_ref(v_decls_3607_);
    return v_res_3611_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(
    mut v_n_3612_: *mut leanh::LeanObject,
    mut v_as_3613_: *mut leanh::LeanObject,
    mut v_i_3614_: usize,
    mut v_stop_3615_: usize,
) -> u8 {
    let mut v___x_3616_: u8 = 0;
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: u8 = 0;
    let mut v___x_3620_: usize = 0;
    let mut v___x_3621_: usize = 0;
    let mut v___x_3623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3616_ = lean_usize_dec_eq(v_i_3614_, v_stop_3615_);
                if v___x_3616_ == 0 {
                    v___x_3617_ = lean_array_uget_borrowed(v_as_3613_, v_i_3614_);
                    v___x_3618_ = l_Lean_IR_Decl_name(v___x_3617_);
                    v___x_3619_ = lean_name_eq(v___x_3618_, v_n_3612_);
                    leanh::lean_dec(v___x_3618_);
                    if v___x_3619_ == 0 {
                        v___x_3620_ = 1usize;
                        v___x_3621_ = lean_usize_add(v_i_3614_, v___x_3620_);
                        v_i_3614_ = v___x_3621_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3619_;
                    }
                } else {
                    v___x_3623_ = 0;
                    return v___x_3623_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(
    mut v_n_3624_: *mut leanh::LeanObject,
    mut v_as_3625_: *mut leanh::LeanObject,
    mut v_i_3626_: *mut leanh::LeanObject,
    mut v_stop_3627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3628_: usize = 0;
    let mut v_stop_boxed_3629_: usize = 0;
    let mut v_res_3630_: u8 = 0;
    let mut v_r_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3628_ = leanh::lean_unbox_usize(v_i_3626_);
    leanh::lean_dec(v_i_3626_);
    v_stop_boxed_3629_ = leanh::lean_unbox_usize(v_stop_3627_);
    leanh::lean_dec(v_stop_3627_);
    v_res_3630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_3624_, v_as_3625_, v_i_boxed_3628_, v_stop_boxed_3629_);
    leanh::lean_dec_ref(v_as_3625_);
    leanh::lean_dec(v_n_3624_);
    v_r_3631_ = leanh::lean_box((v_res_3630_) as usize);
    return v_r_3631_;
}
pub unsafe fn l_Lean_IR_containsDecl_x27___redArg(
    mut v_n_3632_: *mut leanh::LeanObject,
    mut v_decls_3633_: *mut leanh::LeanObject,
    mut v_a_3634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    v___x_3636_ = leanh::lean_unsigned_to_nat(0);
    v___x_3637_ = lean_array_get_size(v_decls_3633_);
    v___x_3638_ = lean_nat_dec_lt(v___x_3636_, v___x_3637_);
    if v___x_3638_ == 0 {
        let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3639_ = l_Lean_IR_containsDecl___redArg(v_n_3632_, v_a_3634_);
        return v___x_3639_;
    } else {
        if v___x_3638_ == 0 {
            let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3640_ = l_Lean_IR_containsDecl___redArg(v_n_3632_, v_a_3634_);
            return v___x_3640_;
        } else {
            let mut v___x_3641_: usize = 0;
            let mut v___x_3642_: usize = 0;
            let mut v___x_3643_: u8 = 0;
            v___x_3641_ = 0usize;
            v___x_3642_ = lean_usize_of_nat(v___x_3637_);
            v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_3632_, v_decls_3633_, v___x_3641_, v___x_3642_);
            if v___x_3643_ == 0 {
                let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3644_ = l_Lean_IR_containsDecl___redArg(v_n_3632_, v_a_3634_);
                return v___x_3644_;
            } else {
                let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_n_3632_);
                v___x_3645_ = leanh::lean_box((v___x_3643_) as usize);
                v___x_3646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3646_, 0, v___x_3645_);
                return v___x_3646_;
            }
        }
    }
}
pub unsafe fn l_Lean_IR_containsDecl_x27___redArg___boxed(
    mut v_n_3647_: *mut leanh::LeanObject,
    mut v_decls_3648_: *mut leanh::LeanObject,
    mut v_a_3649_: *mut leanh::LeanObject,
    mut v_a_3650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3651_ = l_Lean_IR_containsDecl_x27___redArg(v_n_3647_, v_decls_3648_, v_a_3649_);
    leanh::lean_dec(v_a_3649_);
    leanh::lean_dec_ref(v_decls_3648_);
    return v_res_3651_;
}
pub unsafe fn l_Lean_IR_containsDecl_x27(
    mut v_n_3652_: *mut leanh::LeanObject,
    mut v_decls_3653_: *mut leanh::LeanObject,
    mut v_a_3654_: *mut leanh::LeanObject,
    mut v_a_3655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3657_ = l_Lean_IR_containsDecl_x27___redArg(v_n_3652_, v_decls_3653_, v_a_3655_);
    return v___x_3657_;
}
pub unsafe fn l_Lean_IR_containsDecl_x27___boxed(
    mut v_n_3658_: *mut leanh::LeanObject,
    mut v_decls_3659_: *mut leanh::LeanObject,
    mut v_a_3660_: *mut leanh::LeanObject,
    mut v_a_3661_: *mut leanh::LeanObject,
    mut v_a_3662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3663_ = l_Lean_IR_containsDecl_x27(v_n_3658_, v_decls_3659_, v_a_3660_, v_a_3661_);
    leanh::lean_dec(v_a_3661_);
    leanh::lean_dec_ref(v_a_3660_);
    leanh::lean_dec_ref(v_decls_3659_);
    return v_res_3663_;
}
pub unsafe fn l_Lean_IR_getDecl_x27(
    mut v_n_3664_: *mut leanh::LeanObject,
    mut v_decls_3665_: *mut leanh::LeanObject,
    mut v_a_3666_: *mut leanh::LeanObject,
    mut v_a_3667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v_val_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: u8 = 0;
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_n_3664_);
                v___x_3669_ = l_Lean_IR_findDecl_x27___redArg(v_n_3664_, v_decls_3665_, v_a_3667_);
                v_a_3670_ = leanh::lean_ctor_get(v___x_3669_, 0);
                v_isSharedCheck_3687_ = (!leanh::lean_is_exclusive(v___x_3669_)) as u8;
                if v_isSharedCheck_3687_ == 0 {
                    v___x_3672_ = v___x_3669_;
                    v_isShared_3673_ = v_isSharedCheck_3687_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3670_);
                    leanh::lean_dec(v___x_3669_);
                    v___x_3672_ = leanh::lean_box(0);
                    v_isShared_3673_ = v_isSharedCheck_3687_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3670_) == 1 {
                    leanh::lean_dec(v_n_3664_);
                    v_val_3674_ = leanh::lean_ctor_get(v_a_3670_, 0);
                    leanh::lean_inc(v_val_3674_);
                    leanh::lean_dec_ref_known(v_a_3670_, 1);
                    if v_isShared_3673_ == 0 {
                        leanh::lean_ctor_set(v___x_3672_, 0, v_val_3674_);
                        v___x_3676_ = v___x_3672_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_val_3674_);
                        v___x_3676_ = v_reuseFailAlloc_3677_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3672_);
                    leanh::lean_dec(v_a_3670_);
                    v___x_3678_ = l_Lean_IR_getDecl___closed__0;
                    v___x_3679_ = 1;
                    v___x_3680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_n_3664_,
                        v___x_3679_,
                    );
                    v___x_3681_ = lean_string_append(v___x_3678_, v___x_3680_);
                    leanh::lean_dec_ref(v___x_3680_);
                    v___x_3682_ = l_Lean_IR_getDecl___closed__1;
                    v___x_3683_ = lean_string_append(v___x_3681_, v___x_3682_);
                    v___x_3684_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3684_, 0, v___x_3683_);
                    v___x_3685_ = l_Lean_MessageData_ofFormat(v___x_3684_);
                    v___x_3686_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(
                        v___x_3685_,
                        v_a_3666_,
                        v_a_3667_,
                    );
                    return v___x_3686_;
                }
            }
            2 => {
                return v___x_3676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_getDecl_x27___boxed(
    mut v_n_3688_: *mut leanh::LeanObject,
    mut v_decls_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_a_3691_: *mut leanh::LeanObject,
    mut v_a_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lean_IR_getDecl_x27(v_n_3688_, v_decls_3689_, v_a_3690_, v_a_3691_);
    leanh::lean_dec(v_a_3691_);
    leanh::lean_dec_ref(v_a_3690_);
    leanh::lean_dec_ref(v_decls_3689_);
    return v_res_3693_;
}
pub unsafe fn lean_decl_get_sorry_dep(
    mut v_env_3694_: *mut leanh::LeanObject,
    mut v_declName_3695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3696_ = l_Lean_IR_findEnvDecl(v_env_3694_, v_declName_3695_);
    if leanh::lean_obj_tag(v___x_3696_) == 1 {
        let mut v_val_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3697_ = leanh::lean_ctor_get(v___x_3696_, 0);
        leanh::lean_inc(v_val_3697_);
        leanh::lean_dec_ref_known(v___x_3696_, 1);
        if leanh::lean_obj_tag(v_val_3697_) == 0 {
            let mut v_info_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_info_3698_ = leanh::lean_ctor_get(v_val_3697_, 4);
            leanh::lean_inc(v_info_3698_);
            leanh::lean_dec_ref_known(v_val_3697_, 5);
            return v_info_3698_;
        } else {
            let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_3697_);
            v___x_3699_ = leanh::lean_box(0);
            return v___x_3699_;
        }
    } else {
        let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3696_);
        v___x_3700_ = leanh::lean_box(0);
        return v___x_3700_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(
    mut v_env_3701_: *mut leanh::LeanObject,
    mut v_level_3702_: u8,
    mut v_includeDecls_3703_: u8,
    mut v_as_3704_: *mut leanh::LeanObject,
    mut v_i_3705_: usize,
    mut v_stop_3706_: usize,
    mut v_b_3707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: usize = 0;
    let mut v___x_3711_: usize = 0;
    let mut v___x_3713_: u8 = 0;
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: u8 = 0;
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3713_ = lean_usize_dec_eq(v_i_3705_, v_stop_3706_);
                if v___x_3713_ == 0 {
                    v___x_3714_ = lean_array_uget_borrowed(v_as_3704_, v_i_3705_);
                    if v_includeDecls_3703_ == 0 {
                        v___x_3724_ = 1;
                        leanh::lean_inc(v___x_3714_);
                        leanh::lean_inc_ref(v_env_3701_);
                        v___x_3725_ =
                            l_Lean_Environment_contains(v_env_3701_, v___x_3714_, v___x_3724_);
                        if v___x_3725_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            v___y_3709_ = v_b_3707_;
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3701_);
                    return v_b_3707_;
                }
            }
            1 => {
                v___x_3710_ = 1usize;
                v___x_3711_ = lean_usize_add(v_i_3705_, v___x_3710_);
                v_i_3705_ = v___x_3711_;
                v_b_3707_ = v___y_3709_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3716_ == 0 {
                    leanh::lean_inc_ref(v_env_3701_);
                    v___x_3717_ = l_Lean_isDeclMeta(v_env_3701_, v___x_3714_);
                    if v___x_3717_ == 0 {
                        v___y_3709_ = v_b_3707_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_3714_);
                        v___x_3718_ = lean_array_push(v_b_3707_, v___x_3714_);
                        v___y_3709_ = v___x_3718_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___x_3714_);
                    v___x_3719_ = lean_array_push(v_b_3707_, v___x_3714_);
                    v___y_3709_ = v___x_3719_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3721_ = 2;
                v___x_3722_ = l_Lean_instDecidableEqOLeanLevel(v_level_3702_, v___x_3721_);
                if v___x_3722_ == 0 {
                    leanh::lean_inc_ref(v_env_3701_);
                    v___x_3723_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_3701_, v___x_3714_);
                    v___y_3716_ = v___x_3723_;
                    state = 2;
                    continue;
                } else {
                    v___y_3716_ = v___x_3722_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(
    mut v_env_3726_: *mut leanh::LeanObject,
    mut v_level_3727_: *mut leanh::LeanObject,
    mut v_includeDecls_3728_: *mut leanh::LeanObject,
    mut v_as_3729_: *mut leanh::LeanObject,
    mut v_i_3730_: *mut leanh::LeanObject,
    mut v_stop_3731_: *mut leanh::LeanObject,
    mut v_b_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_level_boxed_3733_: u8 = 0;
    let mut v_includeDecls_boxed_3734_: u8 = 0;
    let mut v_i_boxed_3735_: usize = 0;
    let mut v_stop_boxed_3736_: usize = 0;
    let mut v_res_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_level_boxed_3733_ = (leanh::lean_unbox(v_level_3727_) as u8);
    v_includeDecls_boxed_3734_ = (leanh::lean_unbox(v_includeDecls_3728_) as u8);
    v_i_boxed_3735_ = leanh::lean_unbox_usize(v_i_3730_);
    leanh::lean_dec(v_i_3730_);
    v_stop_boxed_3736_ = leanh::lean_unbox_usize(v_stop_3731_);
    leanh::lean_dec(v_stop_3731_);
    v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_3726_, v_level_boxed_3733_, v_includeDecls_boxed_3734_, v_as_3729_, v_i_boxed_3735_, v_stop_boxed_3736_, v_b_3732_);
    leanh::lean_dec_ref(v_as_3729_);
    return v_res_3737_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(
    mut v_sz_3738_: usize,
    mut v_i_3739_: usize,
    mut v_bs_3740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3741_: u8 = 0;
    let mut v_v_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: usize = 0;
    let mut v___x_3747_: usize = 0;
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3741_ = lean_usize_dec_lt(v_i_3739_, v_sz_3738_);
                if v___x_3741_ == 0 {
                    return v_bs_3740_;
                } else {
                    v_v_3742_ = lean_array_uget(v_bs_3740_, v_i_3739_);
                    v___x_3743_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3744_ = lean_array_uset(v_bs_3740_, v_i_3739_, v___x_3743_);
                    v___x_3745_ = l_Lean_IR_Decl_name(v_v_3742_);
                    leanh::lean_dec(v_v_3742_);
                    v___x_3746_ = 1usize;
                    v___x_3747_ = lean_usize_add(v_i_3739_, v___x_3746_);
                    v___x_3748_ = lean_array_uset(v_bs_x27_3744_, v_i_3739_, v___x_3745_);
                    v_i_3739_ = v___x_3747_;
                    v_bs_3740_ = v___x_3748_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(
    mut v_sz_3750_: *mut leanh::LeanObject,
    mut v_i_3751_: *mut leanh::LeanObject,
    mut v_bs_3752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3753_: usize = 0;
    let mut v_i_boxed_3754_: usize = 0;
    let mut v_res_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3753_ = leanh::lean_unbox_usize(v_sz_3750_);
    leanh::lean_dec(v_sz_3750_);
    v_i_boxed_3754_ = leanh::lean_unbox_usize(v_i_3751_);
    leanh::lean_dec(v_i_3751_);
    v_res_3755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_3753_, v_i_boxed_3754_, v_bs_3752_);
    return v_res_3755_;
}
pub unsafe fn lean_get_ir_extra_const_names(
    mut v_env_3758_: *mut leanh::LeanObject,
    mut v_level_3759_: u8,
    mut v_includeDecls_3760_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3767_: usize = 0;
    let mut v___x_3768_: usize = 0;
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: u8 = 0;
    v___x_3761_ = l_Lean_IR_declMapExt;
    v_toEnvExtension_3762_ = leanh::lean_ctor_get(v___x_3761_, 0);
    v_asyncMode_3763_ = leanh::lean_ctor_get(v_toEnvExtension_3762_, 2);
    v___x_3764_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once
        ),
        _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2,
    );
    leanh::lean_inc_ref(v_env_3758_);
    v___x_3765_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v___x_3764_,
        v___x_3761_,
        v_env_3758_,
        v_asyncMode_3763_,
    );
    v___x_3766_ = lean_array_mk(v___x_3765_);
    v_sz_3767_ = lean_array_size(v___x_3766_);
    v___x_3768_ = 0usize;
    v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_3767_, v___x_3768_, v___x_3766_);
    v___x_3770_ = leanh::lean_unsigned_to_nat(0);
    v___x_3771_ = lean_array_get_size(v___x_3769_);
    v___x_3772_ =
        l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0;
    v___x_3773_ = lean_nat_dec_lt(v___x_3770_, v___x_3771_);
    if v___x_3773_ == 0 {
        leanh::lean_dec_ref(v___x_3769_);
        leanh::lean_dec_ref(v_env_3758_);
        return v___x_3772_;
    } else {
        let mut v___x_3774_: u8 = 0;
        v___x_3774_ = lean_nat_dec_le(v___x_3771_, v___x_3771_);
        if v___x_3774_ == 0 {
            if v___x_3773_ == 0 {
                leanh::lean_dec_ref(v___x_3769_);
                leanh::lean_dec_ref(v_env_3758_);
                return v___x_3772_;
            } else {
                let mut v___x_3775_: usize = 0;
                let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3775_ = lean_usize_of_nat(v___x_3771_);
                v___x_3776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_3758_, v_level_3759_, v_includeDecls_3760_, v___x_3769_, v___x_3768_, v___x_3775_, v___x_3772_);
                leanh::lean_dec_ref(v___x_3769_);
                return v___x_3776_;
            }
        } else {
            let mut v___x_3777_: usize = 0;
            let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3777_ = lean_usize_of_nat(v___x_3771_);
            v___x_3778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_3758_, v_level_3759_, v_includeDecls_3760_, v___x_3769_, v___x_3768_, v___x_3777_, v___x_3772_);
            leanh::lean_dec_ref(v___x_3769_);
            return v___x_3778_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(
    mut v_env_3779_: *mut leanh::LeanObject,
    mut v_level_3780_: *mut leanh::LeanObject,
    mut v_includeDecls_3781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_level_boxed_3782_: u8 = 0;
    let mut v_includeDecls_boxed_3783_: u8 = 0;
    let mut v_res_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_level_boxed_3782_ = (leanh::lean_unbox(v_level_3780_) as u8);
    v_includeDecls_boxed_3783_ = (leanh::lean_unbox(v_includeDecls_3781_) as u8);
    v_res_3784_ =
        lean_get_ir_extra_const_names(v_env_3779_, v_level_boxed_3782_, v_includeDecls_boxed_3783_);
    return v_res_3784_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_CompilerM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_3612076334____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_IR_declMapExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_IR_declMapExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_CompilerM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_CompilerM(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_ExportAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_CompilerM(builtin);
}