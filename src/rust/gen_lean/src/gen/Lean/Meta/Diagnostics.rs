// Lean compiler output
// Module: Lean.Meta.Diagnostics
// Imports: Lean.Meta.Basic Lean.PrettyPrinter
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_diagnostics_threshold, l_Lean_isDiagnosticsEnabled___redArg,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_lt___boxed};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_Node_isEmpty___redArg, l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_forIn___redArg, l_Lean_PersistentHashMap_insert___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_Kernel_getDiagnostics, l_Lean_Kernel_setDiagnostics,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_maxSynthPendingDepth,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Instances::l_Lean_Meta_isInstanceCore;
use crate::r#gen::Lean::PrettyPrinter::{
    initialize_Lean_PrettyPrinter, l_Lean_MessageData_ofConst,
    runtime_initialize_Lean_PrettyPrinter,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReducibilityAttrs::lean_get_reducibility_status;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__10_value:
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
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_subCounters___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_subCounters___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_subCounters___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_subCounters___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value:
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
static mut l_Lean_Meta_instInhabitedDiagSummary_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedDiagSummary_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedDiagSummary_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedDiagSummary: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSummary___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_lt___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_mkDiagSummary___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummary___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSummary___closed__1_value: leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkDiagSummary___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummary___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [114, 101, 100, 117, 99, 116, 105, 111, 110, 0],
};
static mut l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0_value)
                as *mut leanh::LeanObject,
            16626236724633252301 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__0_value:
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
    m_fun: l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 121, 112, 101, 95, 99, 108, 97, 115, 115, 0],
};
static mut l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1_value)
            as *mut leanh::LeanObject,
        9097021930341754798 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkDiagSynthPendingFailure___closed__0_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_mkDiagSynthPendingFailure___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_mkDiagSynthPendingFailure___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSynthPendingFailure___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_appendSection___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [32, 40, 109, 97, 120, 58, 32, 0],
    };
static mut l_Lean_Meta_appendSection___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_appendSection___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_appendSection___closed__1_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [44, 32, 110, 117, 109, 58, 32, 0],
    };
static mut l_Lean_Meta_appendSection___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_appendSection___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_appendSection___closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [41, 58, 0],
    };
static mut l_Lean_Meta_appendSection___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_appendSection___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_reportDiag___lam__1___closed__6_value: leanh::LeanStringObject<7> =
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
        m_data: [100, 101, 102, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__6_value)
                as *mut leanh::LeanObject,
            10404218160629279456 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__8_value: leanh::LeanStringObject<7> =
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
        m_data: [107, 101, 114, 110, 101, 108, 0],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__8_value)
                as *mut leanh::LeanObject,
            4997480113592071246 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__10_value: leanh::LeanStringObject<22> =
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
            117, 110, 102, 111, 108, 100, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
            111, 110, 115, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__11_value: leanh::LeanStringObject<19> =
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
            117, 110, 102, 111, 108, 100, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115,
            0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__12_value: leanh::LeanStringObject<32> =
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
            117, 110, 102, 111, 108, 100, 101, 100, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101,
            32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__13_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            117, 115, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__14_value: leanh::LeanStringObject<51> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            109, 97, 120, 32, 115, 121, 110, 116, 104, 32, 112, 101, 110, 100, 105, 110, 103, 32,
            102, 97, 105, 108, 117, 114, 101, 115, 32, 40, 109, 97, 120, 83, 121, 110, 116, 104,
            80, 101, 110, 100, 105, 110, 103, 68, 101, 112, 116, 104, 58, 32, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__15_value: leanh::LeanStringObject<49> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 49,
        m_capacity: 49,
        m_length: 48,
        m_data: [
            41, 44, 32, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32,
            109, 97, 120, 83, 121, 110, 116, 104, 80, 101, 110, 100, 105, 110, 103, 68, 101, 112,
            116, 104, 32, 60, 108, 105, 109, 105, 116, 62, 96, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__16_value: leanh::LeanStringObject<36> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            104, 101, 117, 114, 105, 115, 116, 105, 99, 32, 102, 111, 114, 32, 115, 111, 108, 118,
            105, 110, 103, 32, 96, 102, 32, 97, 32, 61, 63, 61, 32, 102, 32, 98, 96, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__17_value: leanh::LeanStringObject<75> =
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
            65, 120, 105, 111, 109, 115, 32, 40, 112, 111, 115, 115, 105, 98, 108, 121, 32, 105,
            109, 112, 111, 114, 116, 101, 100, 32, 110, 111, 110, 45, 101, 120, 112, 111, 115, 101,
            100, 32, 100, 101, 102, 115, 41, 32, 116, 104, 97, 116, 32, 119, 101, 114, 101, 32,
            116, 114, 105, 101, 100, 32, 116, 111, 32, 98, 101, 32, 117, 110, 102, 111, 108, 100,
            101, 100, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__18_value: leanh::LeanStringObject<89> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 89,
        m_capacity: 89,
        m_length: 88,
        m_data: [
            117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105,
            97, 103, 110, 111, 115, 116, 105, 99, 115, 46, 116, 104, 114, 101, 115, 104, 111, 108,
            100, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 99, 111, 110, 116, 114, 111, 108,
            32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 102, 111, 114, 32, 114, 101, 112,
            111, 114, 116, 105, 110, 103, 32, 99, 111, 117, 110, 116, 101, 114, 115, 0,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__19_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_reportDiag___lam__1___closed__21_value: leanh::LeanStringObject<5> =
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
        m_data: [100, 105, 97, 103, 0],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__22_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__21_value)
                as *mut leanh::LeanObject,
            2816192749436305809 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_reportDiag___lam__1___closed__24_value: leanh::LeanStringObject<12> =
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
        m_data: [68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__25_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__25_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__0(
    mut v_threshold_2423_: *mut leanh::LeanObject,
    mut v_p_2424_: *mut leanh::LeanObject,
    mut v_x_2425_: *mut leanh::LeanObject,
    mut v_____s_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    v_fst_2427_ = leanh::lean_ctor_get(v_x_2425_, 0);
    v_snd_2428_ = leanh::lean_ctor_get(v_x_2425_, 1);
    v___x_2429_ = lean_nat_dec_lt(v_threshold_2423_, v_snd_2428_);
    if v___x_2429_ == 0 {
        let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_x_2425_);
        leanh::lean_dec_ref(v_p_2424_);
        v___x_2430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2430_, 0, v_____s_2426_);
        return v___x_2430_;
    } else {
        let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2432_: u8 = 0;
        leanh::lean_inc(v_fst_2427_);
        v___x_2431_ = leanh::lean_apply_1(v_p_2424_, v_fst_2427_);
        v___x_2432_ = (leanh::lean_unbox(v___x_2431_) as u8);
        if v___x_2432_ == 0 {
            let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_x_2425_);
            v___x_2433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2433_, 0, v_____s_2426_);
            return v___x_2433_;
        } else {
            let mut v_r_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_r_2434_ = lean_array_push(v_____s_2426_, v_x_2425_);
            v___x_2435_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2435_, 0, v_r_2434_);
            return v___x_2435_;
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__0___boxed(
    mut v_threshold_2436_: *mut leanh::LeanObject,
    mut v_p_2437_: *mut leanh::LeanObject,
    mut v_x_2438_: *mut leanh::LeanObject,
    mut v_____s_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2440_ = l_Lean_Meta_collectAboveThreshold___redArg___lam__0(
        v_threshold_2436_,
        v_p_2437_,
        v_x_2438_,
        v_____s_2439_,
    );
    leanh::lean_dec(v_threshold_2436_);
    return v_res_2440_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__1(
    mut v_lt_2441_: *mut leanh::LeanObject,
    mut v_x_2442_: *mut leanh::LeanObject,
    mut v_x_2443_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: u8 = 0;
    v_fst_2444_ = leanh::lean_ctor_get(v_x_2442_, 0);
    leanh::lean_inc(v_fst_2444_);
    v_snd_2445_ = leanh::lean_ctor_get(v_x_2442_, 1);
    leanh::lean_inc(v_snd_2445_);
    leanh::lean_dec_ref(v_x_2442_);
    v_fst_2446_ = leanh::lean_ctor_get(v_x_2443_, 0);
    leanh::lean_inc(v_fst_2446_);
    v_snd_2447_ = leanh::lean_ctor_get(v_x_2443_, 1);
    leanh::lean_inc(v_snd_2447_);
    leanh::lean_dec_ref(v_x_2443_);
    v___x_2448_ = lean_nat_dec_eq(v_snd_2445_, v_snd_2447_);
    if v___x_2448_ == 0 {
        let mut v___x_2449_: u8 = 0;
        leanh::lean_dec(v_fst_2446_);
        leanh::lean_dec(v_fst_2444_);
        leanh::lean_dec_ref(v_lt_2441_);
        v___x_2449_ = lean_nat_dec_lt(v_snd_2447_, v_snd_2445_);
        leanh::lean_dec(v_snd_2445_);
        leanh::lean_dec(v_snd_2447_);
        return v___x_2449_;
    } else {
        let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: u8 = 0;
        leanh::lean_dec(v_snd_2447_);
        leanh::lean_dec(v_snd_2445_);
        v___x_2450_ = leanh::lean_apply_2(v_lt_2441_, v_fst_2444_, v_fst_2446_);
        v___x_2451_ = (leanh::lean_unbox(v___x_2450_) as u8);
        return v___x_2451_;
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__1___boxed(
    mut v_lt_2452_: *mut leanh::LeanObject,
    mut v_x_2453_: *mut leanh::LeanObject,
    mut v_x_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2455_: u8 = 0;
    let mut v_r_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ =
        l_Lean_Meta_collectAboveThreshold___redArg___lam__1(v_lt_2452_, v_x_2453_, v_x_2454_);
    v_r_2456_ = leanh::lean_box((v_res_2455_) as usize);
    return v_r_2456_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg(
    mut v_counters_2478_: *mut leanh::LeanObject,
    mut v_threshold_2479_: *mut leanh::LeanObject,
    mut v_p_2480_: *mut leanh::LeanObject,
    mut v_lt_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v___f_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: u8 = 0;
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2482_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_collectAboveThreshold___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2482_, 0, v_threshold_2479_);
                leanh::lean_closure_set(v___f_2482_, 1, v_p_2480_);
                v___x_2483_ = l_Lean_Meta_collectAboveThreshold___redArg___closed__9;
                v___x_2484_ = leanh::lean_unsigned_to_nat(0);
                v_r_2485_ = l_Lean_Meta_collectAboveThreshold___redArg___closed__10;
                v___x_2486_ = l_Lean_PersistentHashMap_forIn___redArg(
                    v___x_2483_,
                    v_counters_2478_,
                    v_r_2485_,
                    v___f_2482_,
                );
                v___x_2487_ = lean_array_get_size(v___x_2486_);
                v___x_2488_ = lean_nat_dec_eq(v___x_2487_, v___x_2484_);
                if v___x_2488_ == 0 {
                    v___f_2489_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_collectAboveThreshold___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2489_, 0, v_lt_2481_);
                    v___x_2490_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2491_ = lean_nat_sub(v___x_2487_, v___x_2490_);
                    v___x_2497_ = lean_nat_dec_le(v___x_2484_, v___x_2491_);
                    if v___x_2497_ == 0 {
                        leanh::lean_inc(v___x_2491_);
                        v___y_2493_ = v___x_2491_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2493_ = v___x_2484_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_lt_2481_);
                    return v___x_2486_;
                }
            }
            1 => {
                v___x_2494_ = lean_nat_dec_le(v___y_2493_, v___x_2491_);
                if v___x_2494_ == 0 {
                    leanh::lean_dec(v___x_2491_);
                    leanh::lean_inc(v___y_2493_);
                    v___x_2495_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        leanh::lean_box(0),
                        v___f_2489_,
                        v___x_2487_,
                        v___x_2486_,
                        v___y_2493_,
                        v___y_2493_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    leanh::lean_dec(v___y_2493_);
                    return v___x_2495_;
                } else {
                    v___x_2496_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        leanh::lean_box(0),
                        v___f_2489_,
                        v___x_2487_,
                        v___x_2486_,
                        v___y_2493_,
                        v___x_2491_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    leanh::lean_dec(v___x_2491_);
                    return v___x_2496_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___boxed(
    mut v_counters_2498_: *mut leanh::LeanObject,
    mut v_threshold_2499_: *mut leanh::LeanObject,
    mut v_p_2500_: *mut leanh::LeanObject,
    mut v_lt_2501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Lean_Meta_collectAboveThreshold___redArg(
        v_counters_2498_,
        v_threshold_2499_,
        v_p_2500_,
        v_lt_2501_,
    );
    leanh::lean_dec_ref(v_counters_2498_);
    return v_res_2502_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold(
    mut v_00_u03b1_2503_: *mut leanh::LeanObject,
    mut v_inst_2504_: *mut leanh::LeanObject,
    mut v_inst_2505_: *mut leanh::LeanObject,
    mut v_counters_2506_: *mut leanh::LeanObject,
    mut v_threshold_2507_: *mut leanh::LeanObject,
    mut v_p_2508_: *mut leanh::LeanObject,
    mut v_lt_2509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = l_Lean_Meta_collectAboveThreshold___redArg(
        v_counters_2506_,
        v_threshold_2507_,
        v_p_2508_,
        v_lt_2509_,
    );
    return v___x_2510_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___boxed(
    mut v_00_u03b1_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_inst_2513_: *mut leanh::LeanObject,
    mut v_counters_2514_: *mut leanh::LeanObject,
    mut v_threshold_2515_: *mut leanh::LeanObject,
    mut v_p_2516_: *mut leanh::LeanObject,
    mut v_lt_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2518_ = l_Lean_Meta_collectAboveThreshold(
        v_00_u03b1_2511_,
        v_inst_2512_,
        v_inst_2513_,
        v_counters_2514_,
        v_threshold_2515_,
        v_p_2516_,
        v_lt_2517_,
    );
    leanh::lean_dec_ref(v_counters_2514_);
    leanh::lean_dec_ref(v_inst_2513_);
    leanh::lean_dec_ref(v_inst_2512_);
    return v_res_2518_;
}
pub unsafe fn l_Lean_Meta_subCounters___redArg___lam__0(
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v_inst_2520_: *mut leanh::LeanObject,
    mut v_oldCounters_2521_: *mut leanh::LeanObject,
    mut v_x_2522_: *mut leanh::LeanObject,
    mut v_____s_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v_result_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2524_ = leanh::lean_ctor_get(v_x_2522_, 0);
                leanh::lean_inc_n(v_fst_2524_, 2);
                v_snd_2525_ = leanh::lean_ctor_get(v_x_2522_, 1);
                leanh::lean_inc(v_snd_2525_);
                leanh::lean_dec_ref(v_x_2522_);
                leanh::lean_inc_ref(v_inst_2520_);
                leanh::lean_inc_ref(v_inst_2519_);
                v___x_2526_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v_inst_2519_,
                    v_inst_2520_,
                    v_oldCounters_2521_,
                    v_fst_2524_,
                );
                if leanh::lean_obj_tag(v___x_2526_) == 1 {
                    v_val_2527_ = leanh::lean_ctor_get(v___x_2526_, 0);
                    v_isSharedCheck_2536_ = (!leanh::lean_is_exclusive(v___x_2526_)) as u8;
                    if v_isSharedCheck_2536_ == 0 {
                        v___x_2529_ = v___x_2526_;
                        v_isShared_2530_ = v_isSharedCheck_2536_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2527_);
                        leanh::lean_dec(v___x_2526_);
                        v___x_2529_ = leanh::lean_box(0);
                        v_isShared_2530_ = v_isSharedCheck_2536_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2526_);
                    v_result_2537_ = l_Lean_PersistentHashMap_insert___redArg(
                        v_inst_2519_,
                        v_inst_2520_,
                        v_____s_2523_,
                        v_fst_2524_,
                        v_snd_2525_,
                    );
                    v___x_2538_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2538_, 0, v_result_2537_);
                    return v___x_2538_;
                }
            }
            1 => {
                v___x_2531_ = lean_nat_sub(v_snd_2525_, v_val_2527_);
                leanh::lean_dec(v_val_2527_);
                leanh::lean_dec(v_snd_2525_);
                v_result_2532_ = l_Lean_PersistentHashMap_insert___redArg(
                    v_inst_2519_,
                    v_inst_2520_,
                    v_____s_2523_,
                    v_fst_2524_,
                    v___x_2531_,
                );
                if v_isShared_2530_ == 0 {
                    leanh::lean_ctor_set(v___x_2529_, 0, v_result_2532_);
                    v___x_2534_ = v___x_2529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_result_2532_);
                    v___x_2534_ = v_reuseFailAlloc_2535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_subCounters___redArg___lam__0___boxed(
    mut v_inst_2539_: *mut leanh::LeanObject,
    mut v_inst_2540_: *mut leanh::LeanObject,
    mut v_oldCounters_2541_: *mut leanh::LeanObject,
    mut v_x_2542_: *mut leanh::LeanObject,
    mut v_____s_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_Lean_Meta_subCounters___redArg___lam__0(
        v_inst_2539_,
        v_inst_2540_,
        v_oldCounters_2541_,
        v_x_2542_,
        v_____s_2543_,
    );
    leanh::lean_dec_ref(v_oldCounters_2541_);
    return v_res_2544_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___redArg___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2545_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2545_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___redArg___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___redArg___closed__0_once),
        _init_l_Lean_Meta_subCounters___redArg___closed__0,
    );
    v_result_2547_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v_result_2547_, 0, v___x_2546_);
    return v_result_2547_;
}
pub unsafe fn l_Lean_Meta_subCounters___redArg(
    mut v_inst_2548_: *mut leanh::LeanObject,
    mut v_inst_2549_: *mut leanh::LeanObject,
    mut v_newCounters_2550_: *mut leanh::LeanObject,
    mut v_oldCounters_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2552_ = leanh::lean_alloc_closure(
        l_Lean_Meta_subCounters___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2552_, 0, v_inst_2548_);
    leanh::lean_closure_set(v___f_2552_, 1, v_inst_2549_);
    leanh::lean_closure_set(v___f_2552_, 2, v_oldCounters_2551_);
    v___x_2553_ = l_Lean_Meta_collectAboveThreshold___redArg___closed__9;
    v_result_2554_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___redArg___closed__1_once),
        _init_l_Lean_Meta_subCounters___redArg___closed__1,
    );
    v___x_2555_ = l_Lean_PersistentHashMap_forIn___redArg(
        v___x_2553_,
        v_newCounters_2550_,
        v_result_2554_,
        v___f_2552_,
    );
    return v___x_2555_;
}
pub unsafe fn l_Lean_Meta_subCounters___redArg___boxed(
    mut v_inst_2556_: *mut leanh::LeanObject,
    mut v_inst_2557_: *mut leanh::LeanObject,
    mut v_newCounters_2558_: *mut leanh::LeanObject,
    mut v_oldCounters_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_Lean_Meta_subCounters___redArg(
        v_inst_2556_,
        v_inst_2557_,
        v_newCounters_2558_,
        v_oldCounters_2559_,
    );
    leanh::lean_dec_ref(v_newCounters_2558_);
    return v_res_2560_;
}
pub unsafe fn l_Lean_Meta_subCounters(
    mut v_00_u03b1_2561_: *mut leanh::LeanObject,
    mut v_inst_2562_: *mut leanh::LeanObject,
    mut v_inst_2563_: *mut leanh::LeanObject,
    mut v_newCounters_2564_: *mut leanh::LeanObject,
    mut v_oldCounters_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Lean_Meta_subCounters___redArg(
        v_inst_2562_,
        v_inst_2563_,
        v_newCounters_2564_,
        v_oldCounters_2565_,
    );
    return v___x_2566_;
}
pub unsafe fn l_Lean_Meta_subCounters___boxed(
    mut v_00_u03b1_2567_: *mut leanh::LeanObject,
    mut v_inst_2568_: *mut leanh::LeanObject,
    mut v_inst_2569_: *mut leanh::LeanObject,
    mut v_newCounters_2570_: *mut leanh::LeanObject,
    mut v_oldCounters_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Lean_Meta_subCounters(
        v_00_u03b1_2567_,
        v_inst_2568_,
        v_inst_2569_,
        v_newCounters_2570_,
        v_oldCounters_2571_,
    );
    leanh::lean_dec_ref(v_newCounters_2570_);
    return v_res_2572_;
}
pub unsafe fn l_Lean_Meta_DiagSummary_isEmpty(mut v_s_2580_: *mut leanh::LeanObject) -> u8 {
    let mut v_data_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: u8 = 0;
    v_data_2581_ = leanh::lean_ctor_get(v_s_2580_, 0);
    v___x_2582_ = lean_array_get_size(v_data_2581_);
    v___x_2583_ = leanh::lean_unsigned_to_nat(0);
    v___x_2584_ = lean_nat_dec_eq(v___x_2582_, v___x_2583_);
    return v___x_2584_;
}
pub unsafe fn l_Lean_Meta_DiagSummary_isEmpty___boxed(
    mut v_s_2585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2586_: u8 = 0;
    let mut v_r_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2586_ = l_Lean_Meta_DiagSummary_isEmpty(v_s_2585_);
    leanh::lean_dec_ref(v_s_2585_);
    v_r_2587_ = leanh::lean_box((v_res_2586_) as usize);
    return v_r_2587_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0(
    mut v_opts_2588_: *mut leanh::LeanObject,
    mut v_opt_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2590_ = leanh::lean_ctor_get(v_opt_2589_, 0);
    v_defValue_2591_ = leanh::lean_ctor_get(v_opt_2589_, 1);
    v_map_2592_ = leanh::lean_ctor_get(v_opts_2588_, 0);
    v___x_2593_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2592_,
            v_name_2590_,
        );
    if leanh::lean_obj_tag(v___x_2593_) == 0 {
        leanh::lean_inc(v_defValue_2591_);
        return v_defValue_2591_;
    } else {
        let mut v_val_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2594_ = leanh::lean_ctor_get(v___x_2593_, 0);
        leanh::lean_inc(v_val_2594_);
        leanh::lean_dec_ref_known(v___x_2593_, 1);
        if leanh::lean_obj_tag(v_val_2594_) == 3 {
            let mut v_v_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_2595_ = leanh::lean_ctor_get(v_val_2594_, 0);
            leanh::lean_inc(v_v_2595_);
            leanh::lean_dec_ref_known(v_val_2594_, 1);
            return v_v_2595_;
        } else {
            leanh::lean_dec(v_val_2594_);
            leanh::lean_inc(v_defValue_2591_);
            return v_defValue_2591_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0___boxed(
    mut v_opts_2596_: *mut leanh::LeanObject,
    mut v_opt_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2598_ =
        l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0(v_opts_2596_, v_opt_2597_);
    leanh::lean_dec_ref(v_opt_2597_);
    leanh::lean_dec_ref(v_opts_2596_);
    return v_res_2598_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__5(
    mut v_a_2599_: *mut leanh::LeanObject,
    mut v_a_2600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2606_: u8 = 0;
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2599_) == 0 {
                    v___x_2601_ = l_List_reverse___redArg(v_a_2600_);
                    return v___x_2601_;
                } else {
                    v_head_2602_ = leanh::lean_ctor_get(v_a_2599_, 0);
                    v_tail_2603_ = leanh::lean_ctor_get(v_a_2599_, 1);
                    v_isSharedCheck_2612_ = (!leanh::lean_is_exclusive(v_a_2599_)) as u8;
                    if v_isSharedCheck_2612_ == 0 {
                        v___x_2605_ = v_a_2599_;
                        v_isShared_2606_ = v_isSharedCheck_2612_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2603_);
                        leanh::lean_inc(v_head_2602_);
                        leanh::lean_dec(v_a_2599_);
                        v___x_2605_ = leanh::lean_box(0);
                        v_isShared_2606_ = v_isSharedCheck_2612_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2607_ = l_Lean_mkLevelParam(v_head_2602_);
                if v_isShared_2606_ == 0 {
                    leanh::lean_ctor_set(v___x_2605_, 1, v_a_2600_);
                    leanh::lean_ctor_set(v___x_2605_, 0, v___x_2607_);
                    v___x_2609_ = v___x_2605_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_a_2600_);
                    v___x_2609_ = v_reuseFailAlloc_2611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2599_ = v_tail_2603_;
                v_a_2600_ = v___x_2609_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2613_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2614_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0);
    v___x_2615_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2615_, 0, v___x_2614_);
    return v___x_2615_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2616_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1);
    v___x_2617_ = leanh::lean_unsigned_to_nat(0);
    v___x_2618_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2618_, 0, v___x_2617_);
    leanh::lean_ctor_set(v___x_2618_, 1, v___x_2617_);
    leanh::lean_ctor_set(v___x_2618_, 2, v___x_2617_);
    leanh::lean_ctor_set(v___x_2618_, 3, v___x_2617_);
    leanh::lean_ctor_set(v___x_2618_, 4, v___x_2616_);
    leanh::lean_ctor_set(v___x_2618_, 5, v___x_2616_);
    leanh::lean_ctor_set(v___x_2618_, 6, v___x_2616_);
    leanh::lean_ctor_set(v___x_2618_, 7, v___x_2616_);
    leanh::lean_ctor_set(v___x_2618_, 8, v___x_2616_);
    leanh::lean_ctor_set(v___x_2618_, 9, v___x_2616_);
    return v___x_2618_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2619_ = leanh::lean_unsigned_to_nat(32);
    v___x_2620_ = lean_mk_empty_array_with_capacity(v___x_2619_);
    v___x_2621_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2621_, 0, v___x_2620_);
    return v___x_2621_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2622_: usize = 0;
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2622_ = 5usize;
    v___x_2623_ = leanh::lean_unsigned_to_nat(0);
    v___x_2624_ = leanh::lean_unsigned_to_nat(32);
    v___x_2625_ = lean_mk_empty_array_with_capacity(v___x_2624_);
    v___x_2626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3);
    v___x_2627_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2627_, 0, v___x_2626_);
    leanh::lean_ctor_set(v___x_2627_, 1, v___x_2625_);
    leanh::lean_ctor_set(v___x_2627_, 2, v___x_2623_);
    leanh::lean_ctor_set(v___x_2627_, 3, v___x_2623_);
    leanh::lean_ctor_set_usize(v___x_2627_, 4, v___x_2622_);
    return v___x_2627_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2628_ = leanh::lean_box(1);
    v___x_2629_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4);
    v___x_2630_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1);
    v___x_2631_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2631_, 0, v___x_2630_);
    leanh::lean_ctor_set(v___x_2631_, 1, v___x_2629_);
    leanh::lean_ctor_set(v___x_2631_, 2, v___x_2628_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2633_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6;
    v___x_2634_ = l_Lean_stringToMessageData(v___x_2633_);
    return v___x_2634_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8;
    v___x_2637_ = l_Lean_stringToMessageData(v___x_2636_);
    return v___x_2637_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10;
    v___x_2640_ = l_Lean_stringToMessageData(v___x_2639_);
    return v___x_2640_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12;
    v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
    return v___x_2643_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14;
    v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2648_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16;
    v___x_2649_ = l_Lean_stringToMessageData(v___x_2648_);
    return v___x_2649_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18;
    v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
    return v___x_2652_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(
    mut v_msg_2653_: *mut leanh::LeanObject,
    mut v_declHint_2654_: *mut leanh::LeanObject,
    mut v___y_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: u8 = 0;
    let mut v_isExporting_2660_: u8 = 0;
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2657_ = lean_st_ref_get(v___y_2655_);
                v_env_2658_ = leanh::lean_ctor_get(v___x_2657_, 0);
                leanh::lean_inc_ref(v_env_2658_);
                leanh::lean_dec(v___x_2657_);
                v___x_2659_ = l_Lean_Name_isAnonymous(v_declHint_2654_);
                if v___x_2659_ == 0 {
                    v_isExporting_2660_ = leanh::lean_ctor_get_uint8(
                        v_env_2658_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2660_ == 0 {
                        leanh::lean_dec_ref(v_env_2658_);
                        leanh::lean_dec(v_declHint_2654_);
                        v___x_2661_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2661_, 0, v_msg_2653_);
                        return v___x_2661_;
                    } else {
                        leanh::lean_inc_ref(v_env_2658_);
                        v___x_2662_ = l_Lean_Environment_setExporting(v_env_2658_, v___x_2659_);
                        leanh::lean_inc(v_declHint_2654_);
                        leanh::lean_inc_ref(v___x_2662_);
                        v___x_2663_ = l_Lean_Environment_contains(
                            v___x_2662_,
                            v_declHint_2654_,
                            v_isExporting_2660_,
                        );
                        if v___x_2663_ == 0 {
                            leanh::lean_dec_ref(v___x_2662_);
                            leanh::lean_dec_ref(v_env_2658_);
                            leanh::lean_dec(v_declHint_2654_);
                            v___x_2664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2664_, 0, v_msg_2653_);
                            return v___x_2664_;
                        } else {
                            v___x_2665_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2);
                            v___x_2666_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5);
                            v___x_2667_ = l_Lean_Options_empty;
                            v___x_2668_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2668_, 0, v___x_2662_);
                            leanh::lean_ctor_set(v___x_2668_, 1, v___x_2665_);
                            leanh::lean_ctor_set(v___x_2668_, 2, v___x_2666_);
                            leanh::lean_ctor_set(v___x_2668_, 3, v___x_2667_);
                            leanh::lean_inc(v_declHint_2654_);
                            v___x_2669_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2654_, v___x_2659_);
                            v_c_2670_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_2670_, 0, v___x_2668_);
                            leanh::lean_ctor_set(v_c_2670_, 1, v___x_2669_);
                            v___x_2671_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2658_,
                                v_declHint_2654_,
                            );
                            if leanh::lean_obj_tag(v___x_2671_) == 0 {
                                leanh::lean_dec_ref(v_env_2658_);
                                leanh::lean_dec(v_declHint_2654_);
                                v___x_2672_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7);
                                v___x_2673_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2673_, 0, v___x_2672_);
                                leanh::lean_ctor_set(v___x_2673_, 1, v_c_2670_);
                                v___x_2674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9);
                                v___x_2675_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2675_, 0, v___x_2673_);
                                leanh::lean_ctor_set(v___x_2675_, 1, v___x_2674_);
                                v___x_2676_ = l_Lean_MessageData_note(v___x_2675_);
                                v___x_2677_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2677_, 0, v_msg_2653_);
                                leanh::lean_ctor_set(v___x_2677_, 1, v___x_2676_);
                                v___x_2678_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2678_, 0, v___x_2677_);
                                return v___x_2678_;
                            } else {
                                v_val_2679_ = leanh::lean_ctor_get(v___x_2671_, 0);
                                v_isSharedCheck_2714_ =
                                    (!leanh::lean_is_exclusive(v___x_2671_)) as u8;
                                if v_isSharedCheck_2714_ == 0 {
                                    v___x_2681_ = v___x_2671_;
                                    v_isShared_2682_ = v_isSharedCheck_2714_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_2679_);
                                    leanh::lean_dec(v___x_2671_);
                                    v___x_2681_ = leanh::lean_box(0);
                                    v_isShared_2682_ = v_isSharedCheck_2714_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2658_);
                    leanh::lean_dec(v_declHint_2654_);
                    v___x_2715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2715_, 0, v_msg_2653_);
                    return v___x_2715_;
                }
            }
            1 => {
                v___x_2683_ = leanh::lean_box(0);
                v___x_2684_ = l_Lean_Environment_header(v_env_2658_);
                leanh::lean_dec_ref(v_env_2658_);
                v___x_2685_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2684_);
                v_mod_2686_ = lean_array_get(v___x_2683_, v___x_2685_, v_val_2679_);
                leanh::lean_dec(v_val_2679_);
                leanh::lean_dec_ref(v___x_2685_);
                v___x_2687_ = l_Lean_isPrivateName(v_declHint_2654_);
                leanh::lean_dec(v_declHint_2654_);
                if v___x_2687_ == 0 {
                    v___x_2688_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11);
                    v___x_2689_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2689_, 0, v___x_2688_);
                    leanh::lean_ctor_set(v___x_2689_, 1, v_c_2670_);
                    v___x_2690_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13);
                    v___x_2691_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2691_, 0, v___x_2689_);
                    leanh::lean_ctor_set(v___x_2691_, 1, v___x_2690_);
                    v___x_2692_ = l_Lean_MessageData_ofName(v_mod_2686_);
                    v___x_2693_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2693_, 0, v___x_2691_);
                    leanh::lean_ctor_set(v___x_2693_, 1, v___x_2692_);
                    v___x_2694_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15);
                    v___x_2695_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2695_, 0, v___x_2693_);
                    leanh::lean_ctor_set(v___x_2695_, 1, v___x_2694_);
                    v___x_2696_ = l_Lean_MessageData_note(v___x_2695_);
                    v___x_2697_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2697_, 0, v_msg_2653_);
                    leanh::lean_ctor_set(v___x_2697_, 1, v___x_2696_);
                    if v_isShared_2682_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2681_, 0);
                        leanh::lean_ctor_set(v___x_2681_, 0, v___x_2697_);
                        v___x_2699_ = v___x_2681_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
                        v___x_2699_ = v_reuseFailAlloc_2700_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2701_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7);
                    v___x_2702_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2702_, 0, v___x_2701_);
                    leanh::lean_ctor_set(v___x_2702_, 1, v_c_2670_);
                    v___x_2703_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17);
                    v___x_2704_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2704_, 0, v___x_2702_);
                    leanh::lean_ctor_set(v___x_2704_, 1, v___x_2703_);
                    v___x_2705_ = l_Lean_MessageData_ofName(v_mod_2686_);
                    v___x_2706_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2706_, 0, v___x_2704_);
                    leanh::lean_ctor_set(v___x_2706_, 1, v___x_2705_);
                    v___x_2707_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19);
                    v___x_2708_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_2706_);
                    leanh::lean_ctor_set(v___x_2708_, 1, v___x_2707_);
                    v___x_2709_ = l_Lean_MessageData_note(v___x_2708_);
                    v___x_2710_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2710_, 0, v_msg_2653_);
                    leanh::lean_ctor_set(v___x_2710_, 1, v___x_2709_);
                    if v_isShared_2682_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2681_, 0);
                        leanh::lean_ctor_set(v___x_2681_, 0, v___x_2710_);
                        v___x_2712_ = v___x_2681_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2713_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
                        v___x_2712_ = v_reuseFailAlloc_2713_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2699_;
            }
            3 => {
                return v___x_2712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___boxed(
    mut v_msg_2716_: *mut leanh::LeanObject,
    mut v_declHint_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2720_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(v_msg_2716_, v_declHint_2717_, v___y_2718_);
    leanh::lean_dec(v___y_2718_);
    return v_res_2720_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15(
    mut v_msg_2721_: *mut leanh::LeanObject,
    mut v_declHint_2722_: *mut leanh::LeanObject,
    mut v___y_2723_: *mut leanh::LeanObject,
    mut v___y_2724_: *mut leanh::LeanObject,
    mut v___y_2725_: *mut leanh::LeanObject,
    mut v___y_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2728_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(v_msg_2721_, v_declHint_2722_, v___y_2726_);
                v_a_2729_ = leanh::lean_ctor_get(v___x_2728_, 0);
                v_isSharedCheck_2738_ = (!leanh::lean_is_exclusive(v___x_2728_)) as u8;
                if v_isSharedCheck_2738_ == 0 {
                    v___x_2731_ = v___x_2728_;
                    v_isShared_2732_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2729_);
                    leanh::lean_dec(v___x_2728_);
                    v___x_2731_ = leanh::lean_box(0);
                    v_isShared_2732_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2733_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2734_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2734_, 0, v___x_2733_);
                leanh::lean_ctor_set(v___x_2734_, 1, v_a_2729_);
                if v_isShared_2732_ == 0 {
                    leanh::lean_ctor_set(v___x_2731_, 0, v___x_2734_);
                    v___x_2736_ = v___x_2731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
                    v___x_2736_ = v_reuseFailAlloc_2737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15___boxed(
    mut v_msg_2739_: *mut leanh::LeanObject,
    mut v_declHint_2740_: *mut leanh::LeanObject,
    mut v___y_2741_: *mut leanh::LeanObject,
    mut v___y_2742_: *mut leanh::LeanObject,
    mut v___y_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
    mut v___y_2745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2746_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15(v_msg_2739_, v_declHint_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
    leanh::lean_dec(v___y_2744_);
    leanh::lean_dec_ref(v___y_2743_);
    leanh::lean_dec(v___y_2742_);
    leanh::lean_dec_ref(v___y_2741_);
    return v_res_2746_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(
    mut v_msgData_2747_: *mut leanh::LeanObject,
    mut v___y_2748_: *mut leanh::LeanObject,
    mut v___y_2749_: *mut leanh::LeanObject,
    mut v___y_2750_: *mut leanh::LeanObject,
    mut v___y_2751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2753_ = lean_st_ref_get(v___y_2751_);
    v_env_2754_ = leanh::lean_ctor_get(v___x_2753_, 0);
    leanh::lean_inc_ref(v_env_2754_);
    leanh::lean_dec(v___x_2753_);
    v___x_2755_ = lean_st_ref_get(v___y_2749_);
    v_mctx_2756_ = leanh::lean_ctor_get(v___x_2755_, 0);
    leanh::lean_inc_ref(v_mctx_2756_);
    leanh::lean_dec(v___x_2755_);
    v_lctx_2757_ = leanh::lean_ctor_get(v___y_2748_, 2);
    v_options_2758_ = leanh::lean_ctor_get(v___y_2750_, 2);
    leanh::lean_inc_ref(v_options_2758_);
    leanh::lean_inc_ref(v_lctx_2757_);
    v___x_2759_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2759_, 0, v_env_2754_);
    leanh::lean_ctor_set(v___x_2759_, 1, v_mctx_2756_);
    leanh::lean_ctor_set(v___x_2759_, 2, v_lctx_2757_);
    leanh::lean_ctor_set(v___x_2759_, 3, v_options_2758_);
    v___x_2760_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2760_, 0, v___x_2759_);
    leanh::lean_ctor_set(v___x_2760_, 1, v_msgData_2747_);
    v___x_2761_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2761_, 0, v___x_2760_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19___boxed(
    mut v_msgData_2762_: *mut leanh::LeanObject,
    mut v___y_2763_: *mut leanh::LeanObject,
    mut v___y_2764_: *mut leanh::LeanObject,
    mut v___y_2765_: *mut leanh::LeanObject,
    mut v___y_2766_: *mut leanh::LeanObject,
    mut v___y_2767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2768_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(v_msgData_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
    leanh::lean_dec(v___y_2766_);
    leanh::lean_dec_ref(v___y_2765_);
    leanh::lean_dec(v___y_2764_);
    leanh::lean_dec_ref(v___y_2763_);
    return v_res_2768_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(
    mut v_msg_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2775_ = leanh::lean_ctor_get(v___y_2772_, 5);
                v___x_2776_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
                v_a_2777_ = leanh::lean_ctor_get(v___x_2776_, 0);
                v_isSharedCheck_2785_ = (!leanh::lean_is_exclusive(v___x_2776_)) as u8;
                if v_isSharedCheck_2785_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    v_isShared_2780_ = v_isSharedCheck_2785_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2777_);
                    leanh::lean_dec(v___x_2776_);
                    v___x_2779_ = leanh::lean_box(0);
                    v_isShared_2780_ = v_isSharedCheck_2785_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2775_);
                v___x_2781_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2781_, 0, v_ref_2775_);
                leanh::lean_ctor_set(v___x_2781_, 1, v_a_2777_);
                if v_isShared_2780_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2779_, 1);
                    leanh::lean_ctor_set(v___x_2779_, 0, v___x_2781_);
                    v___x_2783_ = v___x_2779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
                    v___x_2783_ = v_reuseFailAlloc_2784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg___boxed(
    mut v_msg_2786_: *mut leanh::LeanObject,
    mut v___y_2787_: *mut leanh::LeanObject,
    mut v___y_2788_: *mut leanh::LeanObject,
    mut v___y_2789_: *mut leanh::LeanObject,
    mut v___y_2790_: *mut leanh::LeanObject,
    mut v___y_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(v_msg_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
    leanh::lean_dec(v___y_2790_);
    leanh::lean_dec_ref(v___y_2789_);
    leanh::lean_dec(v___y_2788_);
    leanh::lean_dec_ref(v___y_2787_);
    return v_res_2792_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(
    mut v_ref_2793_: *mut leanh::LeanObject,
    mut v_msg_2794_: *mut leanh::LeanObject,
    mut v___y_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2812_: u8 = 0;
    let mut v_cancelTk_x3f_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2814_: u8 = 0;
    let mut v_inheritedTraceOptions_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2800_ = leanh::lean_ctor_get(v___y_2797_, 0);
    v_fileMap_2801_ = leanh::lean_ctor_get(v___y_2797_, 1);
    v_options_2802_ = leanh::lean_ctor_get(v___y_2797_, 2);
    v_currRecDepth_2803_ = leanh::lean_ctor_get(v___y_2797_, 3);
    v_maxRecDepth_2804_ = leanh::lean_ctor_get(v___y_2797_, 4);
    v_ref_2805_ = leanh::lean_ctor_get(v___y_2797_, 5);
    v_currNamespace_2806_ = leanh::lean_ctor_get(v___y_2797_, 6);
    v_openDecls_2807_ = leanh::lean_ctor_get(v___y_2797_, 7);
    v_initHeartbeats_2808_ = leanh::lean_ctor_get(v___y_2797_, 8);
    v_maxHeartbeats_2809_ = leanh::lean_ctor_get(v___y_2797_, 9);
    v_quotContext_2810_ = leanh::lean_ctor_get(v___y_2797_, 10);
    v_currMacroScope_2811_ = leanh::lean_ctor_get(v___y_2797_, 11);
    v_diag_2812_ = leanh::lean_ctor_get_uint8(
        v___y_2797_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2813_ = leanh::lean_ctor_get(v___y_2797_, 12);
    v_suppressElabErrors_2814_ = leanh::lean_ctor_get_uint8(
        v___y_2797_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2815_ = leanh::lean_ctor_get(v___y_2797_, 13);
    v_ref_2816_ = l_Lean_replaceRef(v_ref_2793_, v_ref_2805_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2815_);
    leanh::lean_inc(v_cancelTk_x3f_2813_);
    leanh::lean_inc(v_currMacroScope_2811_);
    leanh::lean_inc(v_quotContext_2810_);
    leanh::lean_inc(v_maxHeartbeats_2809_);
    leanh::lean_inc(v_initHeartbeats_2808_);
    leanh::lean_inc(v_openDecls_2807_);
    leanh::lean_inc(v_currNamespace_2806_);
    leanh::lean_inc(v_maxRecDepth_2804_);
    leanh::lean_inc(v_currRecDepth_2803_);
    leanh::lean_inc_ref(v_options_2802_);
    leanh::lean_inc_ref(v_fileMap_2801_);
    leanh::lean_inc_ref(v_fileName_2800_);
    v___x_2817_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2817_, 0, v_fileName_2800_);
    leanh::lean_ctor_set(v___x_2817_, 1, v_fileMap_2801_);
    leanh::lean_ctor_set(v___x_2817_, 2, v_options_2802_);
    leanh::lean_ctor_set(v___x_2817_, 3, v_currRecDepth_2803_);
    leanh::lean_ctor_set(v___x_2817_, 4, v_maxRecDepth_2804_);
    leanh::lean_ctor_set(v___x_2817_, 5, v_ref_2816_);
    leanh::lean_ctor_set(v___x_2817_, 6, v_currNamespace_2806_);
    leanh::lean_ctor_set(v___x_2817_, 7, v_openDecls_2807_);
    leanh::lean_ctor_set(v___x_2817_, 8, v_initHeartbeats_2808_);
    leanh::lean_ctor_set(v___x_2817_, 9, v_maxHeartbeats_2809_);
    leanh::lean_ctor_set(v___x_2817_, 10, v_quotContext_2810_);
    leanh::lean_ctor_set(v___x_2817_, 11, v_currMacroScope_2811_);
    leanh::lean_ctor_set(v___x_2817_, 12, v_cancelTk_x3f_2813_);
    leanh::lean_ctor_set(v___x_2817_, 13, v_inheritedTraceOptions_2815_);
    leanh::lean_ctor_set_uint8(
        v___x_2817_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2812_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2817_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2814_,
    );
    v___x_2818_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(v_msg_2794_, v___y_2795_, v___y_2796_, v___x_2817_, v___y_2798_);
    leanh::lean_dec_ref_known(v___x_2817_, 14);
    return v___x_2818_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg___boxed(
    mut v_ref_2819_: *mut leanh::LeanObject,
    mut v_msg_2820_: *mut leanh::LeanObject,
    mut v___y_2821_: *mut leanh::LeanObject,
    mut v___y_2822_: *mut leanh::LeanObject,
    mut v___y_2823_: *mut leanh::LeanObject,
    mut v___y_2824_: *mut leanh::LeanObject,
    mut v___y_2825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2826_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(v_ref_2819_, v_msg_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
    leanh::lean_dec(v___y_2824_);
    leanh::lean_dec_ref(v___y_2823_);
    leanh::lean_dec(v___y_2822_);
    leanh::lean_dec_ref(v___y_2821_);
    leanh::lean_dec(v_ref_2819_);
    return v_res_2826_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(
    mut v_ref_2827_: *mut leanh::LeanObject,
    mut v_msg_2828_: *mut leanh::LeanObject,
    mut v_declHint_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
    mut v___y_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15(v_msg_2828_, v_declHint_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
    v_a_2836_ = leanh::lean_ctor_get(v___x_2835_, 0);
    leanh::lean_inc(v_a_2836_);
    leanh::lean_dec_ref(v___x_2835_);
    v___x_2837_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(v_ref_2827_, v_a_2836_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
    return v___x_2837_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg___boxed(
    mut v_ref_2838_: *mut leanh::LeanObject,
    mut v_msg_2839_: *mut leanh::LeanObject,
    mut v_declHint_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
    mut v___y_2845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2846_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(v_ref_2838_, v_msg_2839_, v_declHint_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
    leanh::lean_dec(v___y_2844_);
    leanh::lean_dec_ref(v___y_2843_);
    leanh::lean_dec(v___y_2842_);
    leanh::lean_dec_ref(v___y_2841_);
    leanh::lean_dec(v_ref_2838_);
    return v_res_2846_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0;
    v___x_2849_ = l_Lean_stringToMessageData(v___x_2848_);
    return v___x_2849_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2;
    v___x_2852_ = l_Lean_stringToMessageData(v___x_2851_);
    return v___x_2852_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(
    mut v_ref_2853_: *mut leanh::LeanObject,
    mut v_constName_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1);
    v___x_2861_ = 0;
    leanh::lean_inc(v_constName_2854_);
    v___x_2862_ = l_Lean_MessageData_ofConstName(v_constName_2854_, v___x_2861_);
    v___x_2863_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2863_, 0, v___x_2860_);
    leanh::lean_ctor_set(v___x_2863_, 1, v___x_2862_);
    v___x_2864_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3);
    v___x_2865_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2865_, 0, v___x_2863_);
    leanh::lean_ctor_set(v___x_2865_, 1, v___x_2864_);
    v___x_2866_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(v_ref_2853_, v___x_2865_, v_constName_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
    return v___x_2866_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___boxed(
    mut v_ref_2867_: *mut leanh::LeanObject,
    mut v_constName_2868_: *mut leanh::LeanObject,
    mut v___y_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(v_ref_2867_, v_constName_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
    leanh::lean_dec(v___y_2872_);
    leanh::lean_dec_ref(v___y_2871_);
    leanh::lean_dec(v___y_2870_);
    leanh::lean_dec_ref(v___y_2869_);
    leanh::lean_dec(v_ref_2867_);
    return v_res_2874_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(
    mut v_constName_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2881_ = leanh::lean_ctor_get(v___y_2878_, 5);
    v___x_2882_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(v_ref_2881_, v_constName_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
    return v___x_2882_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_constName_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(v_constName_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    leanh::lean_dec(v___y_2887_);
    leanh::lean_dec_ref(v___y_2886_);
    leanh::lean_dec(v___y_2885_);
    leanh::lean_dec_ref(v___y_2884_);
    return v_res_2889_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4(
    mut v_constName_2890_: *mut leanh::LeanObject,
    mut v___y_2891_: *mut leanh::LeanObject,
    mut v___y_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2896_ = lean_st_ref_get(v___y_2894_);
                v_env_2897_ = leanh::lean_ctor_get(v___x_2896_, 0);
                leanh::lean_inc_ref(v_env_2897_);
                leanh::lean_dec(v___x_2896_);
                v___x_2898_ = 0;
                leanh::lean_inc(v_constName_2890_);
                v___x_2899_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2897_,
                    v_constName_2890_,
                    v___x_2898_,
                );
                if leanh::lean_obj_tag(v___x_2899_) == 0 {
                    v___x_2900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(v_constName_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
                    return v___x_2900_;
                } else {
                    leanh::lean_dec(v_constName_2890_);
                    v_val_2901_ = leanh::lean_ctor_get(v___x_2899_, 0);
                    v_isSharedCheck_2908_ = (!leanh::lean_is_exclusive(v___x_2899_)) as u8;
                    if v_isSharedCheck_2908_ == 0 {
                        v___x_2903_ = v___x_2899_;
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2901_);
                        leanh::lean_dec(v___x_2899_);
                        v___x_2903_ = leanh::lean_box(0);
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2904_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2903_, 0);
                    v___x_2906_ = v___x_2903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_val_2901_);
                    v___x_2906_ = v_reuseFailAlloc_2907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4___boxed(
    mut v_constName_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
    mut v___y_2913_: *mut leanh::LeanObject,
    mut v___y_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4(v_constName_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
    leanh::lean_dec(v___y_2913_);
    leanh::lean_dec_ref(v___y_2912_);
    leanh::lean_dec(v___y_2911_);
    leanh::lean_dec_ref(v___y_2910_);
    return v_res_2915_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2(
    mut v_constName_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
    mut v___y_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v_levelParams_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_a_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_constName_2916_);
                v___x_2922_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4(v_constName_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
                if leanh::lean_obj_tag(v___x_2922_) == 0 {
                    v_a_2923_ = leanh::lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2934_ = (!leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2934_ == 0 {
                        v___x_2925_ = v___x_2922_;
                        v_isShared_2926_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2923_);
                        leanh::lean_dec(v___x_2922_);
                        v___x_2925_ = leanh::lean_box(0);
                        v_isShared_2926_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_constName_2916_);
                    v_a_2935_ = leanh::lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2942_ = (!leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2942_ == 0 {
                        v___x_2937_ = v___x_2922_;
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2935_);
                        leanh::lean_dec(v___x_2922_);
                        v___x_2937_ = leanh::lean_box(0);
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_2927_ = leanh::lean_ctor_get(v_a_2923_, 1);
                leanh::lean_inc(v_levelParams_2927_);
                leanh::lean_dec(v_a_2923_);
                v___x_2928_ = leanh::lean_box(0);
                v___x_2929_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__5(v_levelParams_2927_, v___x_2928_);
                v___x_2930_ = l_Lean_mkConst(v_constName_2916_, v___x_2929_);
                if v_isShared_2926_ == 0 {
                    leanh::lean_ctor_set(v___x_2925_, 0, v___x_2930_);
                    v___x_2932_ = v___x_2925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
                    v___x_2932_ = v_reuseFailAlloc_2933_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2932_;
            }
            3 => {
                if v_isShared_2938_ == 0 {
                    v___x_2940_ = v___x_2937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
                    v___x_2940_ = v_reuseFailAlloc_2941_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2___boxed(
    mut v_constName_2943_: *mut leanh::LeanObject,
    mut v___y_2944_: *mut leanh::LeanObject,
    mut v___y_2945_: *mut leanh::LeanObject,
    mut v___y_2946_: *mut leanh::LeanObject,
    mut v___y_2947_: *mut leanh::LeanObject,
    mut v___y_2948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2(
        v_constName_2943_,
        v___y_2944_,
        v___y_2945_,
        v___y_2946_,
        v___y_2947_,
    );
    leanh::lean_dec(v___y_2947_);
    leanh::lean_dec_ref(v___y_2946_);
    leanh::lean_dec(v___y_2945_);
    leanh::lean_dec_ref(v___y_2944_);
    return v_res_2949_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0()
-> f64 {
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: f64 = 0.0;
    v___x_2950_ = leanh::lean_unsigned_to_nat(0);
    v___x_2951_ = lean_float_of_nat(v___x_2950_);
    return v___x_2951_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2;
    v___x_2955_ = l_Lean_stringToMessageData(v___x_2954_);
    return v___x_2955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3(
    mut v_cls_2956_: *mut leanh::LeanObject,
    mut v_as_2957_: *mut leanh::LeanObject,
    mut v_sz_2958_: usize,
    mut v_i_2959_: usize,
    mut v_b_2960_: *mut leanh::LeanObject,
    mut v___y_2961_: *mut leanh::LeanObject,
    mut v___y_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
    mut v___y_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2973_: u8 = 0;
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: f64 = 0.0;
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: usize = 0;
    let mut v_reuseFailAlloc_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2966_ = lean_usize_dec_lt(v_i_2959_, v_sz_2958_);
                if v___x_2966_ == 0 {
                    leanh::lean_dec(v_cls_2956_);
                    v___x_2967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2967_, 0, v_b_2960_);
                    return v___x_2967_;
                } else {
                    v_a_2968_ = lean_array_uget(v_as_2957_, v_i_2959_);
                    v_fst_2969_ = leanh::lean_ctor_get(v_a_2968_, 0);
                    v_snd_2970_ = leanh::lean_ctor_get(v_a_2968_, 1);
                    v_isSharedCheck_3003_ = (!leanh::lean_is_exclusive(v_a_2968_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2972_ = v_a_2968_;
                        v_isShared_2973_ = v_isSharedCheck_3003_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2970_);
                        leanh::lean_inc(v_fst_2969_);
                        leanh::lean_dec(v_a_2968_);
                        v___x_2972_ = leanh::lean_box(0);
                        v_isShared_2973_ = v_isSharedCheck_3003_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2974_ =
                    l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2(
                        v_fst_2969_,
                        v___y_2961_,
                        v___y_2962_,
                        v___y_2963_,
                        v___y_2964_,
                    );
                if leanh::lean_obj_tag(v___x_2974_) == 0 {
                    v_a_2975_ = leanh::lean_ctor_get(v___x_2974_, 0);
                    leanh::lean_inc(v_a_2975_);
                    leanh::lean_dec_ref_known(v___x_2974_, 1);
                    v___x_2976_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__0;
                    v___x_2977_ = leanh::lean_box(0);
                    v___x_2978_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0);
                    v___x_2979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
                    leanh::lean_inc(v_cls_2956_);
                    v___x_2980_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v___x_2980_, 0, v_cls_2956_);
                    leanh::lean_ctor_set(v___x_2980_, 1, v___x_2977_);
                    leanh::lean_ctor_set(v___x_2980_, 2, v___x_2979_);
                    leanh::lean_ctor_set_float(
                        v___x_2980_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_2978_,
                    );
                    leanh::lean_ctor_set_float(
                        v___x_2980_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_2978_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_2980_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v___x_2966_,
                    );
                    v___x_2981_ = l_Lean_MessageData_ofConst(v_a_2975_);
                    v___x_2982_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3);
                    if v_isShared_2973_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2972_, 7);
                        leanh::lean_ctor_set(v___x_2972_, 1, v___x_2982_);
                        leanh::lean_ctor_set(v___x_2972_, 0, v___x_2981_);
                        v___x_2984_ = v___x_2972_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2994_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2981_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2982_);
                        v___x_2984_ = v_reuseFailAlloc_2994_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2972_);
                    leanh::lean_dec(v_snd_2970_);
                    leanh::lean_dec_ref(v_b_2960_);
                    leanh::lean_dec(v_cls_2956_);
                    v_a_2995_ = leanh::lean_ctor_get(v___x_2974_, 0);
                    v_isSharedCheck_3002_ = (!leanh::lean_is_exclusive(v___x_2974_)) as u8;
                    if v_isSharedCheck_3002_ == 0 {
                        v___x_2997_ = v___x_2974_;
                        v_isShared_2998_ = v_isSharedCheck_3002_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2995_);
                        leanh::lean_dec(v___x_2974_);
                        v___x_2997_ = leanh::lean_box(0);
                        v_isShared_2998_ = v_isSharedCheck_3002_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2985_ = l_Nat_reprFast(v_snd_2970_);
                v___x_2986_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2986_, 0, v___x_2985_);
                v___x_2987_ = l_Lean_MessageData_ofFormat(v___x_2986_);
                v___x_2988_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2988_, 0, v___x_2984_);
                leanh::lean_ctor_set(v___x_2988_, 1, v___x_2987_);
                v___x_2989_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2989_, 0, v___x_2980_);
                leanh::lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                leanh::lean_ctor_set(v___x_2989_, 2, v___x_2976_);
                v___x_2990_ = lean_array_push(v_b_2960_, v___x_2989_);
                v___x_2991_ = 1usize;
                v___x_2992_ = lean_usize_add(v_i_2959_, v___x_2991_);
                v_i_2959_ = v___x_2992_;
                v_b_2960_ = v___x_2990_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2998_ == 0 {
                    v___x_3000_ = v___x_2997_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
                    v___x_3000_ = v_reuseFailAlloc_3001_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___boxed(
    mut v_cls_3004_: *mut leanh::LeanObject,
    mut v_as_3005_: *mut leanh::LeanObject,
    mut v_sz_3006_: *mut leanh::LeanObject,
    mut v_i_3007_: *mut leanh::LeanObject,
    mut v_b_3008_: *mut leanh::LeanObject,
    mut v___y_3009_: *mut leanh::LeanObject,
    mut v___y_3010_: *mut leanh::LeanObject,
    mut v___y_3011_: *mut leanh::LeanObject,
    mut v___y_3012_: *mut leanh::LeanObject,
    mut v___y_3013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3014_: usize = 0;
    let mut v_i_boxed_3015_: usize = 0;
    let mut v_res_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3014_ = leanh::lean_unbox_usize(v_sz_3006_);
    leanh::lean_dec(v_sz_3006_);
    v_i_boxed_3015_ = leanh::lean_unbox_usize(v_i_3007_);
    leanh::lean_dec(v_i_3007_);
    v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3(v_cls_3004_, v_as_3005_, v_sz_boxed_3014_, v_i_boxed_3015_, v_b_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
    leanh::lean_dec(v___y_3012_);
    leanh::lean_dec_ref(v___y_3011_);
    leanh::lean_dec(v___y_3010_);
    leanh::lean_dec_ref(v___y_3009_);
    leanh::lean_dec_ref(v_as_3005_);
    return v_res_3016_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(
    mut v_lt_3017_: *mut leanh::LeanObject,
    mut v_hi_3018_: *mut leanh::LeanObject,
    mut v_pivot_3019_: *mut leanh::LeanObject,
    mut v_as_3020_: *mut leanh::LeanObject,
    mut v_i_3021_: *mut leanh::LeanObject,
    mut v_k_3022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3024_: u8 = 0;
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3033_ = lean_nat_dec_lt(v_k_3022_, v_hi_3018_);
                if v___x_3033_ == 0 {
                    leanh::lean_dec(v_k_3022_);
                    leanh::lean_dec_ref(v_pivot_3019_);
                    leanh::lean_dec_ref(v_lt_3017_);
                    v___x_3034_ = lean_array_fswap(v_as_3020_, v_i_3021_, v_hi_3018_);
                    v___x_3035_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3035_, 0, v_i_3021_);
                    leanh::lean_ctor_set(v___x_3035_, 1, v___x_3034_);
                    return v___x_3035_;
                } else {
                    v___x_3036_ = lean_array_fget_borrowed(v_as_3020_, v_k_3022_);
                    v_fst_3037_ = leanh::lean_ctor_get(v___x_3036_, 0);
                    v_snd_3038_ = leanh::lean_ctor_get(v___x_3036_, 1);
                    v_fst_3039_ = leanh::lean_ctor_get(v_pivot_3019_, 0);
                    v_snd_3040_ = leanh::lean_ctor_get(v_pivot_3019_, 1);
                    v___x_3041_ = lean_nat_dec_eq(v_snd_3038_, v_snd_3040_);
                    if v___x_3041_ == 0 {
                        v___x_3042_ = lean_nat_dec_lt(v_snd_3040_, v_snd_3038_);
                        v___y_3024_ = v___x_3042_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_lt_3017_);
                        leanh::lean_inc(v_fst_3039_);
                        leanh::lean_inc(v_fst_3037_);
                        v___x_3043_ =
                            leanh::lean_apply_2(v_lt_3017_, v_fst_3037_, v_fst_3039_);
                        v___x_3044_ = (leanh::lean_unbox(v___x_3043_) as u8);
                        v___y_3024_ = v___x_3044_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3024_ == 0 {
                    v___x_3025_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3026_ = lean_nat_add(v_k_3022_, v___x_3025_);
                    leanh::lean_dec(v_k_3022_);
                    v_k_3022_ = v___x_3026_;
                    state = 0;
                    continue;
                } else {
                    v___x_3028_ = lean_array_fswap(v_as_3020_, v_i_3021_, v_k_3022_);
                    v___x_3029_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3030_ = lean_nat_add(v_i_3021_, v___x_3029_);
                    leanh::lean_dec(v_i_3021_);
                    v___x_3031_ = lean_nat_add(v_k_3022_, v___x_3029_);
                    leanh::lean_dec(v_k_3022_);
                    v_as_3020_ = v___x_3028_;
                    v_i_3021_ = v___x_3030_;
                    v_k_3022_ = v___x_3031_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_lt_3045_: *mut leanh::LeanObject,
    mut v_hi_3046_: *mut leanh::LeanObject,
    mut v_pivot_3047_: *mut leanh::LeanObject,
    mut v_as_3048_: *mut leanh::LeanObject,
    mut v_i_3049_: *mut leanh::LeanObject,
    mut v_k_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_3045_, v_hi_3046_, v_pivot_3047_, v_as_3048_, v_i_3049_, v_k_3050_);
    leanh::lean_dec(v_hi_3046_);
    return v_res_3051_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(
    mut v_lt_3052_: *mut leanh::LeanObject,
    mut v_x_3053_: *mut leanh::LeanObject,
    mut v_x_3054_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    v_fst_3055_ = leanh::lean_ctor_get(v_x_3053_, 0);
    leanh::lean_inc(v_fst_3055_);
    v_snd_3056_ = leanh::lean_ctor_get(v_x_3053_, 1);
    leanh::lean_inc(v_snd_3056_);
    leanh::lean_dec_ref(v_x_3053_);
    v_fst_3057_ = leanh::lean_ctor_get(v_x_3054_, 0);
    leanh::lean_inc(v_fst_3057_);
    v_snd_3058_ = leanh::lean_ctor_get(v_x_3054_, 1);
    leanh::lean_inc(v_snd_3058_);
    leanh::lean_dec_ref(v_x_3054_);
    v___x_3059_ = lean_nat_dec_eq(v_snd_3056_, v_snd_3058_);
    if v___x_3059_ == 0 {
        let mut v___x_3060_: u8 = 0;
        leanh::lean_dec(v_fst_3057_);
        leanh::lean_dec(v_fst_3055_);
        leanh::lean_dec_ref(v_lt_3052_);
        v___x_3060_ = lean_nat_dec_lt(v_snd_3058_, v_snd_3056_);
        leanh::lean_dec(v_snd_3056_);
        leanh::lean_dec(v_snd_3058_);
        return v___x_3060_;
    } else {
        let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3062_: u8 = 0;
        leanh::lean_dec(v_snd_3058_);
        leanh::lean_dec(v_snd_3056_);
        v___x_3061_ = leanh::lean_apply_2(v_lt_3052_, v_fst_3055_, v_fst_3057_);
        v___x_3062_ = (leanh::lean_unbox(v___x_3061_) as u8);
        return v___x_3062_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0___boxed(
    mut v_lt_3063_: *mut leanh::LeanObject,
    mut v_x_3064_: *mut leanh::LeanObject,
    mut v_x_3065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3066_: u8 = 0;
    let mut v_r_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_3063_, v_x_3064_, v_x_3065_);
    v_r_3067_ = leanh::lean_box((v_res_3066_) as usize);
    return v_r_3067_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(
    mut v_lt_3068_: *mut leanh::LeanObject,
    mut v_n_3069_: *mut leanh::LeanObject,
    mut v_as_3070_: *mut leanh::LeanObject,
    mut v_lo_3071_: *mut leanh::LeanObject,
    mut v_hi_3072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: u8 = 0;
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3084_ = lean_nat_dec_lt(v_lo_3071_, v_hi_3072_);
                if v___x_3084_ == 0 {
                    leanh::lean_dec(v_lo_3071_);
                    leanh::lean_dec_ref(v_lt_3068_);
                    return v_as_3070_;
                } else {
                    v___x_3085_ = lean_nat_add(v_lo_3071_, v_hi_3072_);
                    v___x_3086_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_3087_ = lean_nat_shiftr(v___x_3085_, v___x_3086_);
                    leanh::lean_dec(v___x_3085_);
                    v___x_3100_ = lean_array_fget_borrowed(v_as_3070_, v_mid_3087_);
                    v___x_3101_ = lean_array_fget_borrowed(v_as_3070_, v_lo_3071_);
                    leanh::lean_inc(v___x_3101_);
                    leanh::lean_inc(v___x_3100_);
                    leanh::lean_inc_ref(v_lt_3068_);
                    v___x_3102_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_3068_, v___x_3100_, v___x_3101_);
                    if v___x_3102_ == 0 {
                        v___y_3095_ = v_as_3070_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3103_ = lean_array_fswap(v_as_3070_, v_lo_3071_, v_mid_3087_);
                        v___y_3095_ = v___x_3103_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3075_ = lean_array_fget(v___y_3074_, v_hi_3072_);
                leanh::lean_inc_n(v_lo_3071_, 2);
                leanh::lean_inc_ref(v_lt_3068_);
                v___x_3076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_3068_, v_hi_3072_, v_pivot_3075_, v___y_3074_, v_lo_3071_, v_lo_3071_);
                v_fst_3077_ = leanh::lean_ctor_get(v___x_3076_, 0);
                leanh::lean_inc(v_fst_3077_);
                v_snd_3078_ = leanh::lean_ctor_get(v___x_3076_, 1);
                leanh::lean_inc(v_snd_3078_);
                leanh::lean_dec_ref(v___x_3076_);
                v___x_3079_ = lean_nat_dec_le(v_hi_3072_, v_fst_3077_);
                if v___x_3079_ == 0 {
                    leanh::lean_inc_ref(v_lt_3068_);
                    v___x_3080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3068_, v_n_3069_, v_snd_3078_, v_lo_3071_, v_fst_3077_);
                    v___x_3081_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3082_ = lean_nat_add(v_fst_3077_, v___x_3081_);
                    leanh::lean_dec(v_fst_3077_);
                    v_as_3070_ = v___x_3080_;
                    v_lo_3071_ = v___x_3082_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_3077_);
                    leanh::lean_dec(v_lo_3071_);
                    leanh::lean_dec_ref(v_lt_3068_);
                    return v_snd_3078_;
                }
            }
            2 => {
                v___x_3090_ = lean_array_fget_borrowed(v___y_3089_, v_mid_3087_);
                v___x_3091_ = lean_array_fget_borrowed(v___y_3089_, v_hi_3072_);
                leanh::lean_inc(v___x_3091_);
                leanh::lean_inc(v___x_3090_);
                leanh::lean_inc_ref(v_lt_3068_);
                v___x_3092_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_3068_, v___x_3090_, v___x_3091_);
                if v___x_3092_ == 0 {
                    leanh::lean_dec(v_mid_3087_);
                    v___y_3074_ = v___y_3089_;
                    state = 1;
                    continue;
                } else {
                    v___x_3093_ = lean_array_fswap(v___y_3089_, v_mid_3087_, v_hi_3072_);
                    leanh::lean_dec(v_mid_3087_);
                    v___y_3074_ = v___x_3093_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3096_ = lean_array_fget_borrowed(v___y_3095_, v_hi_3072_);
                v___x_3097_ = lean_array_fget_borrowed(v___y_3095_, v_lo_3071_);
                leanh::lean_inc(v___x_3097_);
                leanh::lean_inc(v___x_3096_);
                leanh::lean_inc_ref(v_lt_3068_);
                v___x_3098_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_3068_, v___x_3096_, v___x_3097_);
                if v___x_3098_ == 0 {
                    v___y_3089_ = v___y_3095_;
                    state = 2;
                    continue;
                } else {
                    v___x_3099_ = lean_array_fswap(v___y_3095_, v_lo_3071_, v_hi_3072_);
                    v___y_3089_ = v___x_3099_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___boxed(
    mut v_lt_3104_: *mut leanh::LeanObject,
    mut v_n_3105_: *mut leanh::LeanObject,
    mut v_as_3106_: *mut leanh::LeanObject,
    mut v_lo_3107_: *mut leanh::LeanObject,
    mut v_hi_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3109_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3104_, v_n_3105_, v_as_3106_, v_lo_3107_, v_hi_3108_);
    leanh::lean_dec(v_hi_3108_);
    leanh::lean_dec(v_n_3105_);
    return v_res_3109_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg___lam__0(
    mut v_f_3110_: *mut leanh::LeanObject,
    mut v_s_3111_: *mut leanh::LeanObject,
    mut v_a_3112_: *mut leanh::LeanObject,
    mut v_b_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_a_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3131_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3114_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3114_, 0, v_a_3112_);
                leanh::lean_ctor_set(v___x_3114_, 1, v_b_3113_);
                v___x_3115_ = leanh::lean_apply_2(v_f_3110_, v___x_3114_, v_s_3111_);
                if leanh::lean_obj_tag(v___x_3115_) == 0 {
                    v_a_3116_ = leanh::lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3123_ = (!leanh::lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3123_ == 0 {
                        v___x_3118_ = v___x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3123_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3116_);
                        leanh::lean_dec(v___x_3115_);
                        v___x_3118_ = leanh::lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3123_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3124_ = leanh::lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3131_ = (!leanh::lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3131_ == 0 {
                        v___x_3126_ = v___x_3115_;
                        v_isShared_3127_ = v_isSharedCheck_3131_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3124_);
                        leanh::lean_dec(v___x_3115_);
                        v___x_3126_ = leanh::lean_box(0);
                        v_isShared_3127_ = v_isSharedCheck_3131_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3119_ == 0 {
                    v___x_3121_ = v___x_3118_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3122_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
                    v___x_3121_ = v_reuseFailAlloc_3122_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3121_;
            }
            3 => {
                if v_isShared_3127_ == 0 {
                    v___x_3129_ = v___x_3126_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3130_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
                    v___x_3129_ = v_reuseFailAlloc_3130_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(
    mut v_f_3132_: *mut leanh::LeanObject,
    mut v_keys_3133_: *mut leanh::LeanObject,
    mut v_vals_3134_: *mut leanh::LeanObject,
    mut v_i_3135_: *mut leanh::LeanObject,
    mut v_acc_3136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: u8 = 0;
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3137_ = lean_array_get_size(v_keys_3133_);
                v___x_3138_ = lean_nat_dec_lt(v_i_3135_, v___x_3137_);
                if v___x_3138_ == 0 {
                    leanh::lean_dec(v_i_3135_);
                    leanh::lean_dec_ref(v_f_3132_);
                    v___x_3139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3139_, 0, v_acc_3136_);
                    return v___x_3139_;
                } else {
                    v_k_3140_ = lean_array_fget_borrowed(v_keys_3133_, v_i_3135_);
                    v_v_3141_ = lean_array_fget_borrowed(v_vals_3134_, v_i_3135_);
                    leanh::lean_inc_ref(v_f_3132_);
                    leanh::lean_inc(v_v_3141_);
                    leanh::lean_inc(v_k_3140_);
                    v___x_3142_ =
                        leanh::lean_apply_3(v_f_3132_, v_acc_3136_, v_k_3140_, v_v_3141_);
                    if leanh::lean_obj_tag(v___x_3142_) == 0 {
                        leanh::lean_dec(v_i_3135_);
                        leanh::lean_dec_ref(v_f_3132_);
                        return v___x_3142_;
                    } else {
                        v_a_3143_ = leanh::lean_ctor_get(v___x_3142_, 0);
                        leanh::lean_inc(v_a_3143_);
                        leanh::lean_dec_ref_known(v___x_3142_, 1);
                        v___x_3144_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3145_ = lean_nat_add(v_i_3135_, v___x_3144_);
                        leanh::lean_dec(v_i_3135_);
                        v_i_3135_ = v___x_3145_;
                        v_acc_3136_ = v_a_3143_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg___boxed(
    mut v_f_3147_: *mut leanh::LeanObject,
    mut v_keys_3148_: *mut leanh::LeanObject,
    mut v_vals_3149_: *mut leanh::LeanObject,
    mut v_i_3150_: *mut leanh::LeanObject,
    mut v_acc_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_f_3147_, v_keys_3148_, v_vals_3149_, v_i_3150_, v_acc_3151_);
    leanh::lean_dec_ref(v_vals_3149_);
    leanh::lean_dec_ref(v_keys_3148_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(
    mut v_f_3153_: *mut leanh::LeanObject,
    mut v_x_3154_: *mut leanh::LeanObject,
    mut v_x_3155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: usize = 0;
    let mut v___x_3171_: usize = 0;
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: usize = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v_ks_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3154_) == 0 {
                    v_es_3156_ = leanh::lean_ctor_get(v_x_3154_, 0);
                    v_isSharedCheck_3176_ = (!leanh::lean_is_exclusive(v_x_3154_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3158_ = v_x_3154_;
                        v_isShared_3159_ = v_isSharedCheck_3176_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_3156_);
                        leanh::lean_dec(v_x_3154_);
                        v___x_3158_ = leanh::lean_box(0);
                        v_isShared_3159_ = v_isSharedCheck_3176_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_3177_ = leanh::lean_ctor_get(v_x_3154_, 0);
                    leanh::lean_inc_ref(v_ks_3177_);
                    v_vs_3178_ = leanh::lean_ctor_get(v_x_3154_, 1);
                    leanh::lean_inc_ref(v_vs_3178_);
                    leanh::lean_dec_ref_known(v_x_3154_, 2);
                    v___x_3179_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_f_3153_, v_ks_3177_, v_vs_3178_, v___x_3179_, v_x_3155_);
                    leanh::lean_dec_ref(v_vs_3178_);
                    leanh::lean_dec_ref(v_ks_3177_);
                    return v___x_3180_;
                }
            }
            1 => {
                v___x_3160_ = leanh::lean_unsigned_to_nat(0);
                v___x_3161_ = lean_array_get_size(v_es_3156_);
                v___x_3162_ = lean_nat_dec_lt(v___x_3160_, v___x_3161_);
                if v___x_3162_ == 0 {
                    leanh::lean_dec_ref(v_es_3156_);
                    leanh::lean_dec_ref(v_f_3153_);
                    if v_isShared_3159_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3158_, 1);
                        leanh::lean_ctor_set(v___x_3158_, 0, v_x_3155_);
                        v___x_3164_ = v___x_3158_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3165_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_x_3155_);
                        v___x_3164_ = v_reuseFailAlloc_3165_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3166_ = lean_nat_dec_le(v___x_3161_, v___x_3161_);
                    if v___x_3166_ == 0 {
                        if v___x_3162_ == 0 {
                            leanh::lean_dec_ref(v_es_3156_);
                            leanh::lean_dec_ref(v_f_3153_);
                            if v_isShared_3159_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_3158_, 1);
                                leanh::lean_ctor_set(v___x_3158_, 0, v_x_3155_);
                                v___x_3168_ = v___x_3158_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3169_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_x_3155_);
                                v___x_3168_ = v_reuseFailAlloc_3169_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3158_);
                            v___x_3170_ = 0usize;
                            v___x_3171_ = lean_usize_of_nat(v___x_3161_);
                            v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3153_, v_es_3156_, v___x_3170_, v___x_3171_, v_x_3155_);
                            leanh::lean_dec_ref(v_es_3156_);
                            return v___x_3172_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3158_);
                        v___x_3173_ = 0usize;
                        v___x_3174_ = lean_usize_of_nat(v___x_3161_);
                        v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3153_, v_es_3156_, v___x_3173_, v___x_3174_, v_x_3155_);
                        leanh::lean_dec_ref(v_es_3156_);
                        return v___x_3175_;
                    }
                }
            }
            2 => {
                return v___x_3164_;
            }
            3 => {
                return v___x_3168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(
    mut v_f_3181_: *mut leanh::LeanObject,
    mut v_as_3182_: *mut leanh::LeanObject,
    mut v_i_3183_: usize,
    mut v_stop_3184_: usize,
    mut v_b_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: usize = 0;
    let mut v___x_3189_: usize = 0;
    let mut v___y_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3194_ = lean_usize_dec_eq(v_i_3183_, v_stop_3184_);
                if v___x_3194_ == 0 {
                    v___x_3195_ = lean_array_uget_borrowed(v_as_3182_, v_i_3183_);
                    match leanh::lean_obj_tag(v___x_3195_) {
                        0 => {
                            v_key_3196_ = leanh::lean_ctor_get(v___x_3195_, 0);
                            v_val_3197_ = leanh::lean_ctor_get(v___x_3195_, 1);
                            leanh::lean_inc_ref(v_f_3181_);
                            leanh::lean_inc(v_val_3197_);
                            leanh::lean_inc(v_key_3196_);
                            v___x_3198_ = leanh::lean_apply_3(
                                v_f_3181_,
                                v_b_3185_,
                                v_key_3196_,
                                v_val_3197_,
                            );
                            v___y_3192_ = v___x_3198_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_3199_ = leanh::lean_ctor_get(v___x_3195_, 0);
                            leanh::lean_inc(v_node_3199_);
                            leanh::lean_inc_ref(v_f_3181_);
                            v___x_3200_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_3181_, v_node_3199_, v_b_3185_);
                            v___y_3192_ = v___x_3200_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_3187_ = v_b_3185_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_3181_);
                    v___x_3201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3201_, 0, v_b_3185_);
                    return v___x_3201_;
                }
            }
            1 => {
                v___x_3188_ = 1usize;
                v___x_3189_ = lean_usize_add(v_i_3183_, v___x_3188_);
                v_i_3183_ = v___x_3189_;
                v_b_3185_ = v_a_3187_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3192_) == 0 {
                    leanh::lean_dec_ref(v_f_3181_);
                    return v___y_3192_;
                } else {
                    v_a_3193_ = leanh::lean_ctor_get(v___y_3192_, 0);
                    leanh::lean_inc(v_a_3193_);
                    leanh::lean_dec_ref_known(v___y_3192_, 1);
                    v_a_3187_ = v_a_3193_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg___boxed(
    mut v_f_3202_: *mut leanh::LeanObject,
    mut v_as_3203_: *mut leanh::LeanObject,
    mut v_i_3204_: *mut leanh::LeanObject,
    mut v_stop_3205_: *mut leanh::LeanObject,
    mut v_b_3206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3207_: usize = 0;
    let mut v_stop_boxed_3208_: usize = 0;
    let mut v_res_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3207_ = leanh::lean_unbox_usize(v_i_3204_);
    leanh::lean_dec(v_i_3204_);
    v_stop_boxed_3208_ = leanh::lean_unbox_usize(v_stop_3205_);
    leanh::lean_dec(v_stop_3205_);
    v_res_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3202_, v_as_3203_, v_i_boxed_3207_, v_stop_boxed_3208_, v_b_3206_);
    leanh::lean_dec_ref(v_as_3203_);
    return v_res_3209_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(
    mut v_map_3210_: *mut leanh::LeanObject,
    mut v_init_3211_: *mut leanh::LeanObject,
    mut v_f_3212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3213_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_3213_, 0, v_f_3212_);
    leanh::lean_inc_ref(v_map_3210_);
    v___x_3214_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v___f_3213_, v_map_3210_, v_init_3211_);
    v_a_3215_ = leanh::lean_ctor_get(v___x_3214_, 0);
    leanh::lean_inc(v_a_3215_);
    leanh::lean_dec_ref(v___x_3214_);
    return v_a_3215_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg___boxed(
    mut v_map_3216_: *mut leanh::LeanObject,
    mut v_init_3217_: *mut leanh::LeanObject,
    mut v_f_3218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3219_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(v_map_3216_, v_init_3217_, v_f_3218_);
    leanh::lean_dec_ref(v_map_3216_);
    return v_res_3219_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0(
    mut v_threshold_3220_: *mut leanh::LeanObject,
    mut v_p_3221_: *mut leanh::LeanObject,
    mut v_x_3222_: *mut leanh::LeanObject,
    mut v_____s_3223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    v_fst_3224_ = leanh::lean_ctor_get(v_x_3222_, 0);
    v_snd_3225_ = leanh::lean_ctor_get(v_x_3222_, 1);
    v___x_3226_ = lean_nat_dec_lt(v_threshold_3220_, v_snd_3225_);
    if v___x_3226_ == 0 {
        let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_x_3222_);
        leanh::lean_dec_ref(v_p_3221_);
        v___x_3227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3227_, 0, v_____s_3223_);
        return v___x_3227_;
    } else {
        let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: u8 = 0;
        leanh::lean_inc(v_fst_3224_);
        v___x_3228_ = leanh::lean_apply_1(v_p_3221_, v_fst_3224_);
        v___x_3229_ = (leanh::lean_unbox(v___x_3228_) as u8);
        if v___x_3229_ == 0 {
            let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_x_3222_);
            v___x_3230_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3230_, 0, v_____s_3223_);
            return v___x_3230_;
        } else {
            let mut v_r_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_r_3231_ = lean_array_push(v_____s_3223_, v_x_3222_);
            v___x_3232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3232_, 0, v_r_3231_);
            return v___x_3232_;
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0___boxed(
    mut v_threshold_3233_: *mut leanh::LeanObject,
    mut v_p_3234_: *mut leanh::LeanObject,
    mut v_x_3235_: *mut leanh::LeanObject,
    mut v_____s_3236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3237_ =
        l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0(
            v_threshold_3233_,
            v_p_3234_,
            v_x_3235_,
            v_____s_3236_,
        );
    leanh::lean_dec(v_threshold_3233_);
    return v_res_3237_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1(
    mut v_counters_3240_: *mut leanh::LeanObject,
    mut v_threshold_3241_: *mut leanh::LeanObject,
    mut v_p_3242_: *mut leanh::LeanObject,
    mut v_lt_3243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3244_ = leanh::lean_alloc_closure(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
                leanh::lean_closure_set(v___f_3244_, 0, v_threshold_3241_);
                leanh::lean_closure_set(v___f_3244_, 1, v_p_3242_);
                v___x_3245_ = leanh::lean_unsigned_to_nat(0);
                v_r_3246_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0;
                v___x_3247_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(v_counters_3240_, v_r_3246_, v___f_3244_);
                v___x_3248_ = lean_array_get_size(v___x_3247_);
                v___x_3249_ = lean_nat_dec_eq(v___x_3248_, v___x_3245_);
                if v___x_3249_ == 0 {
                    v___x_3250_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3251_ = lean_nat_sub(v___x_3248_, v___x_3250_);
                    v___x_3257_ = lean_nat_dec_le(v___x_3245_, v___x_3251_);
                    if v___x_3257_ == 0 {
                        leanh::lean_inc(v___x_3251_);
                        v___y_3253_ = v___x_3251_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3253_ = v___x_3245_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_lt_3243_);
                    return v___x_3247_;
                }
            }
            1 => {
                v___x_3254_ = lean_nat_dec_le(v___y_3253_, v___x_3251_);
                if v___x_3254_ == 0 {
                    leanh::lean_dec(v___x_3251_);
                    leanh::lean_inc(v___y_3253_);
                    v___x_3255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3243_, v___x_3248_, v___x_3247_, v___y_3253_, v___y_3253_);
                    leanh::lean_dec(v___y_3253_);
                    return v___x_3255_;
                } else {
                    v___x_3256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3243_, v___x_3248_, v___x_3247_, v___y_3253_, v___x_3251_);
                    leanh::lean_dec(v___x_3251_);
                    return v___x_3256_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___boxed(
    mut v_counters_3258_: *mut leanh::LeanObject,
    mut v_threshold_3259_: *mut leanh::LeanObject,
    mut v_p_3260_: *mut leanh::LeanObject,
    mut v_lt_3261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3262_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1(
        v_counters_3258_,
        v_threshold_3259_,
        v_p_3260_,
        v_lt_3261_,
    );
    leanh::lean_dec_ref(v_counters_3258_);
    return v_res_3262_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummary(
    mut v_cls_3267_: *mut leanh::LeanObject,
    mut v_counters_3268_: *mut leanh::LeanObject,
    mut v_p_3269_: *mut leanh::LeanObject,
    mut v_a_3270_: *mut leanh::LeanObject,
    mut v_a_3271_: *mut leanh::LeanObject,
    mut v_a_3272_: *mut leanh::LeanObject,
    mut v_a_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3284_: usize = 0;
    let mut v___x_3285_: usize = 0;
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3303_: u8 = 0;
    let mut v_unused_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v_a_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3275_ = leanh::lean_ctor_get(v_a_3272_, 2);
                v___x_3276_ = l_Lean_diagnostics_threshold;
                v___x_3277_ = l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0(
                    v_options_3275_,
                    v___x_3276_,
                );
                v___x_3278_ = l_Lean_Meta_mkDiagSummary___closed__0;
                v___x_3279_ =
                    l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1(
                        v_counters_3268_,
                        v___x_3277_,
                        v_p_3269_,
                        v___x_3278_,
                    );
                v___x_3280_ = lean_array_get_size(v___x_3279_);
                v___x_3281_ = leanh::lean_unsigned_to_nat(0);
                v___x_3282_ = lean_nat_dec_eq(v___x_3280_, v___x_3281_);
                if v___x_3282_ == 0 {
                    v___x_3283_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__0;
                    v_sz_3284_ = lean_array_size(v___x_3279_);
                    v___x_3285_ = 0usize;
                    v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3(v_cls_3267_, v___x_3279_, v_sz_3284_, v___x_3285_, v___x_3283_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
                    if leanh::lean_obj_tag(v___x_3286_) == 0 {
                        v_a_3287_ = leanh::lean_ctor_get(v___x_3286_, 0);
                        v_isSharedCheck_3305_ =
                            (!leanh::lean_is_exclusive(v___x_3286_)) as u8;
                        if v_isSharedCheck_3305_ == 0 {
                            v___x_3289_ = v___x_3286_;
                            v_isShared_3290_ = v_isSharedCheck_3305_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3287_);
                            leanh::lean_dec(v___x_3286_);
                            v___x_3289_ = leanh::lean_box(0);
                            v_isShared_3290_ = v_isSharedCheck_3305_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3279_);
                        v_a_3306_ = leanh::lean_ctor_get(v___x_3286_, 0);
                        v_isSharedCheck_3313_ =
                            (!leanh::lean_is_exclusive(v___x_3286_)) as u8;
                        if v_isSharedCheck_3313_ == 0 {
                            v___x_3308_ = v___x_3286_;
                            v_isShared_3309_ = v_isSharedCheck_3313_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3306_);
                            leanh::lean_dec(v___x_3286_);
                            v___x_3308_ = leanh::lean_box(0);
                            v_isShared_3309_ = v_isSharedCheck_3313_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3279_);
                    leanh::lean_dec(v_cls_3267_);
                    v___x_3314_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__1;
                    v___x_3315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3315_, 0, v___x_3314_);
                    return v___x_3315_;
                }
            }
            1 => {
                v___x_3291_ = l_Lean_Meta_mkDiagSummary___closed__1;
                v___x_3292_ = lean_array_get(v___x_3291_, v___x_3279_, v___x_3281_);
                leanh::lean_dec_ref(v___x_3279_);
                v_snd_3293_ = leanh::lean_ctor_get(v___x_3292_, 1);
                v_isSharedCheck_3303_ = (!leanh::lean_is_exclusive(v___x_3292_)) as u8;
                if v_isSharedCheck_3303_ == 0 {
                    v_unused_3304_ = leanh::lean_ctor_get(v___x_3292_, 0);
                    leanh::lean_dec(v_unused_3304_);
                    v___x_3295_ = v___x_3292_;
                    v_isShared_3296_ = v_isSharedCheck_3303_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3293_);
                    leanh::lean_dec(v___x_3292_);
                    v___x_3295_ = leanh::lean_box(0);
                    v_isShared_3296_ = v_isSharedCheck_3303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3296_ == 0 {
                    leanh::lean_ctor_set(v___x_3295_, 0, v_a_3287_);
                    v___x_3298_ = v___x_3295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_snd_3293_);
                    v___x_3298_ = v_reuseFailAlloc_3302_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3290_ == 0 {
                    leanh::lean_ctor_set(v___x_3289_, 0, v___x_3298_);
                    v___x_3300_ = v___x_3289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                    v___x_3300_ = v_reuseFailAlloc_3301_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3300_;
            }
            5 => {
                if v_isShared_3309_ == 0 {
                    v___x_3311_ = v___x_3308_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3312_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
                    v___x_3311_ = v_reuseFailAlloc_3312_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkDiagSummary___boxed(
    mut v_cls_3316_: *mut leanh::LeanObject,
    mut v_counters_3317_: *mut leanh::LeanObject,
    mut v_p_3318_: *mut leanh::LeanObject,
    mut v_a_3319_: *mut leanh::LeanObject,
    mut v_a_3320_: *mut leanh::LeanObject,
    mut v_a_3321_: *mut leanh::LeanObject,
    mut v_a_3322_: *mut leanh::LeanObject,
    mut v_a_3323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3324_ = l_Lean_Meta_mkDiagSummary(
        v_cls_3316_,
        v_counters_3317_,
        v_p_3318_,
        v_a_3319_,
        v_a_3320_,
        v_a_3321_,
        v_a_3322_,
    );
    leanh::lean_dec(v_a_3322_);
    leanh::lean_dec_ref(v_a_3321_);
    leanh::lean_dec(v_a_3320_);
    leanh::lean_dec_ref(v_a_3319_);
    leanh::lean_dec_ref(v_counters_3317_);
    return v_res_3324_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1(
    mut v_00_u03c3_3325_: *mut leanh::LeanObject,
    mut v_00_u03b2_3326_: *mut leanh::LeanObject,
    mut v_map_3327_: *mut leanh::LeanObject,
    mut v_init_3328_: *mut leanh::LeanObject,
    mut v_f_3329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(v_map_3327_, v_init_3328_, v_f_3329_);
    return v___x_3330_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___boxed(
    mut v_00_u03c3_3331_: *mut leanh::LeanObject,
    mut v_00_u03b2_3332_: *mut leanh::LeanObject,
    mut v_map_3333_: *mut leanh::LeanObject,
    mut v_init_3334_: *mut leanh::LeanObject,
    mut v_f_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1(v_00_u03c3_3331_, v_00_u03b2_3332_, v_map_3333_, v_init_3334_, v_f_3335_);
    leanh::lean_dec_ref(v_map_3333_);
    return v_res_3336_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2(
    mut v_lt_3337_: *mut leanh::LeanObject,
    mut v_n_3338_: *mut leanh::LeanObject,
    mut v_as_3339_: *mut leanh::LeanObject,
    mut v_lo_3340_: *mut leanh::LeanObject,
    mut v_hi_3341_: *mut leanh::LeanObject,
    mut v_w_3342_: *mut leanh::LeanObject,
    mut v_hlo_3343_: *mut leanh::LeanObject,
    mut v_hhi_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3345_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3337_, v_n_3338_, v_as_3339_, v_lo_3340_, v_hi_3341_);
    return v___x_3345_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___boxed(
    mut v_lt_3346_: *mut leanh::LeanObject,
    mut v_n_3347_: *mut leanh::LeanObject,
    mut v_as_3348_: *mut leanh::LeanObject,
    mut v_lo_3349_: *mut leanh::LeanObject,
    mut v_hi_3350_: *mut leanh::LeanObject,
    mut v_w_3351_: *mut leanh::LeanObject,
    mut v_hlo_3352_: *mut leanh::LeanObject,
    mut v_hhi_3353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2(v_lt_3346_, v_n_3347_, v_as_3348_, v_lo_3349_, v_hi_3350_, v_w_3351_, v_hlo_3352_, v_hhi_3353_);
    leanh::lean_dec(v_hi_3350_);
    leanh::lean_dec(v_n_3347_);
    return v_res_3354_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2___redArg(
    mut v_map_3355_: *mut leanh::LeanObject,
    mut v_f_3356_: *mut leanh::LeanObject,
    mut v_init_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_3356_, v_map_3355_, v_init_3357_);
    return v___x_3358_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2(
    mut v_00_u03c3_3359_: *mut leanh::LeanObject,
    mut v_00_u03c3_3360_: *mut leanh::LeanObject,
    mut v_00_u03b2_3361_: *mut leanh::LeanObject,
    mut v_map_3362_: *mut leanh::LeanObject,
    mut v_f_3363_: *mut leanh::LeanObject,
    mut v_init_3364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_3363_, v_map_3362_, v_init_3364_);
    return v___x_3365_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4(
    mut v_lt_3366_: *mut leanh::LeanObject,
    mut v_n_3367_: *mut leanh::LeanObject,
    mut v_lo_3368_: *mut leanh::LeanObject,
    mut v_hi_3369_: *mut leanh::LeanObject,
    mut v_hhi_3370_: *mut leanh::LeanObject,
    mut v_pivot_3371_: *mut leanh::LeanObject,
    mut v_as_3372_: *mut leanh::LeanObject,
    mut v_i_3373_: *mut leanh::LeanObject,
    mut v_k_3374_: *mut leanh::LeanObject,
    mut v_ilo_3375_: *mut leanh::LeanObject,
    mut v_ik_3376_: *mut leanh::LeanObject,
    mut v_w_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3378_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_3366_, v_hi_3369_, v_pivot_3371_, v_as_3372_, v_i_3373_, v_k_3374_);
    return v___x_3378_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___boxed(
    mut v_lt_3379_: *mut leanh::LeanObject,
    mut v_n_3380_: *mut leanh::LeanObject,
    mut v_lo_3381_: *mut leanh::LeanObject,
    mut v_hi_3382_: *mut leanh::LeanObject,
    mut v_hhi_3383_: *mut leanh::LeanObject,
    mut v_pivot_3384_: *mut leanh::LeanObject,
    mut v_as_3385_: *mut leanh::LeanObject,
    mut v_i_3386_: *mut leanh::LeanObject,
    mut v_k_3387_: *mut leanh::LeanObject,
    mut v_ilo_3388_: *mut leanh::LeanObject,
    mut v_ik_3389_: *mut leanh::LeanObject,
    mut v_w_3390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4(v_lt_3379_, v_n_3380_, v_lo_3381_, v_hi_3382_, v_hhi_3383_, v_pivot_3384_, v_as_3385_, v_i_3386_, v_k_3387_, v_ilo_3388_, v_ik_3389_, v_w_3390_);
    leanh::lean_dec(v_hi_3382_);
    leanh::lean_dec(v_lo_3381_);
    leanh::lean_dec(v_n_3380_);
    return v_res_3391_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7(
    mut v_00_u03b1_3392_: *mut leanh::LeanObject,
    mut v_constName_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(v_constName_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b1_3400_: *mut leanh::LeanObject,
    mut v_constName_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7(v_00_u03b1_3400_, v_constName_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
    leanh::lean_dec(v___y_3405_);
    leanh::lean_dec_ref(v___y_3404_);
    leanh::lean_dec(v___y_3403_);
    leanh::lean_dec_ref(v___y_3402_);
    return v_res_3407_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5(
    mut v_00_u03c3_3408_: *mut leanh::LeanObject,
    mut v_00_u03c3_3409_: *mut leanh::LeanObject,
    mut v_00_u03b1_3410_: *mut leanh::LeanObject,
    mut v_00_u03b2_3411_: *mut leanh::LeanObject,
    mut v_f_3412_: *mut leanh::LeanObject,
    mut v_x_3413_: *mut leanh::LeanObject,
    mut v_x_3414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_3412_, v_x_3413_, v_x_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10(
    mut v_00_u03b1_3416_: *mut leanh::LeanObject,
    mut v_ref_3417_: *mut leanh::LeanObject,
    mut v_constName_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(v_ref_3417_, v_constName_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
    return v___x_3424_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___boxed(
    mut v_00_u03b1_3425_: *mut leanh::LeanObject,
    mut v_ref_3426_: *mut leanh::LeanObject,
    mut v_constName_3427_: *mut leanh::LeanObject,
    mut v___y_3428_: *mut leanh::LeanObject,
    mut v___y_3429_: *mut leanh::LeanObject,
    mut v___y_3430_: *mut leanh::LeanObject,
    mut v___y_3431_: *mut leanh::LeanObject,
    mut v___y_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3433_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_3425_, v_ref_3426_, v_constName_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
    leanh::lean_dec(v___y_3431_);
    leanh::lean_dec_ref(v___y_3430_);
    leanh::lean_dec(v___y_3429_);
    leanh::lean_dec_ref(v___y_3428_);
    leanh::lean_dec(v_ref_3426_);
    return v_res_3433_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(
    mut v_00_u03b1_3434_: *mut leanh::LeanObject,
    mut v_00_u03b2_3435_: *mut leanh::LeanObject,
    mut v_00_u03c3_3436_: *mut leanh::LeanObject,
    mut v_00_u03c3_3437_: *mut leanh::LeanObject,
    mut v_f_3438_: *mut leanh::LeanObject,
    mut v_as_3439_: *mut leanh::LeanObject,
    mut v_i_3440_: usize,
    mut v_stop_3441_: usize,
    mut v_b_3442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3438_, v_as_3439_, v_i_3440_, v_stop_3441_, v_b_3442_);
    return v___x_3443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(
    mut v_00_u03b1_3444_: *mut leanh::LeanObject,
    mut v_00_u03b2_3445_: *mut leanh::LeanObject,
    mut v_00_u03c3_3446_: *mut leanh::LeanObject,
    mut v_00_u03c3_3447_: *mut leanh::LeanObject,
    mut v_f_3448_: *mut leanh::LeanObject,
    mut v_as_3449_: *mut leanh::LeanObject,
    mut v_i_3450_: *mut leanh::LeanObject,
    mut v_stop_3451_: *mut leanh::LeanObject,
    mut v_b_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3453_: usize = 0;
    let mut v_stop_boxed_3454_: usize = 0;
    let mut v_res_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3453_ = leanh::lean_unbox_usize(v_i_3450_);
    leanh::lean_dec(v_i_3450_);
    v_stop_boxed_3454_ = leanh::lean_unbox_usize(v_stop_3451_);
    leanh::lean_dec(v_stop_3451_);
    v_res_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(v_00_u03b1_3444_, v_00_u03b2_3445_, v_00_u03c3_3446_, v_00_u03c3_3447_, v_f_3448_, v_as_3449_, v_i_boxed_3453_, v_stop_boxed_3454_, v_b_3452_);
    leanh::lean_dec_ref(v_as_3449_);
    return v_res_3455_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10(
    mut v_00_u03c3_3456_: *mut leanh::LeanObject,
    mut v_00_u03c3_3457_: *mut leanh::LeanObject,
    mut v_00_u03b1_3458_: *mut leanh::LeanObject,
    mut v_00_u03b2_3459_: *mut leanh::LeanObject,
    mut v_f_3460_: *mut leanh::LeanObject,
    mut v_keys_3461_: *mut leanh::LeanObject,
    mut v_vals_3462_: *mut leanh::LeanObject,
    mut v_heq_3463_: *mut leanh::LeanObject,
    mut v_i_3464_: *mut leanh::LeanObject,
    mut v_acc_3465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3466_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_f_3460_, v_keys_3461_, v_vals_3462_, v_i_3464_, v_acc_3465_);
    return v___x_3466_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(
    mut v_00_u03c3_3467_: *mut leanh::LeanObject,
    mut v_00_u03c3_3468_: *mut leanh::LeanObject,
    mut v_00_u03b1_3469_: *mut leanh::LeanObject,
    mut v_00_u03b2_3470_: *mut leanh::LeanObject,
    mut v_f_3471_: *mut leanh::LeanObject,
    mut v_keys_3472_: *mut leanh::LeanObject,
    mut v_vals_3473_: *mut leanh::LeanObject,
    mut v_heq_3474_: *mut leanh::LeanObject,
    mut v_i_3475_: *mut leanh::LeanObject,
    mut v_acc_3476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10(v_00_u03c3_3467_, v_00_u03c3_3468_, v_00_u03b1_3469_, v_00_u03b2_3470_, v_f_3471_, v_keys_3472_, v_vals_3473_, v_heq_3474_, v_i_3475_, v_acc_3476_);
    leanh::lean_dec_ref(v_vals_3473_);
    leanh::lean_dec_ref(v_keys_3472_);
    return v_res_3477_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14(
    mut v_00_u03b1_3478_: *mut leanh::LeanObject,
    mut v_ref_3479_: *mut leanh::LeanObject,
    mut v_msg_3480_: *mut leanh::LeanObject,
    mut v_declHint_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
    mut v___y_3484_: *mut leanh::LeanObject,
    mut v___y_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(v_ref_3479_, v_msg_3480_, v_declHint_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___boxed(
    mut v_00_u03b1_3488_: *mut leanh::LeanObject,
    mut v_ref_3489_: *mut leanh::LeanObject,
    mut v_msg_3490_: *mut leanh::LeanObject,
    mut v_declHint_3491_: *mut leanh::LeanObject,
    mut v___y_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
    mut v___y_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3497_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14(v_00_u03b1_3488_, v_ref_3489_, v_msg_3490_, v_declHint_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
    leanh::lean_dec(v___y_3495_);
    leanh::lean_dec_ref(v___y_3494_);
    leanh::lean_dec(v___y_3493_);
    leanh::lean_dec_ref(v___y_3492_);
    leanh::lean_dec(v_ref_3489_);
    return v_res_3497_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16(
    mut v_msg_3498_: *mut leanh::LeanObject,
    mut v_declHint_3499_: *mut leanh::LeanObject,
    mut v___y_3500_: *mut leanh::LeanObject,
    mut v___y_3501_: *mut leanh::LeanObject,
    mut v___y_3502_: *mut leanh::LeanObject,
    mut v___y_3503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(v_msg_3498_, v_declHint_3499_, v___y_3503_);
    return v___x_3505_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___boxed(
    mut v_msg_3506_: *mut leanh::LeanObject,
    mut v_declHint_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16(v_msg_3506_, v_declHint_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
    leanh::lean_dec(v___y_3511_);
    leanh::lean_dec_ref(v___y_3510_);
    leanh::lean_dec(v___y_3509_);
    leanh::lean_dec_ref(v___y_3508_);
    return v_res_3513_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16(
    mut v_00_u03b1_3514_: *mut leanh::LeanObject,
    mut v_ref_3515_: *mut leanh::LeanObject,
    mut v_msg_3516_: *mut leanh::LeanObject,
    mut v___y_3517_: *mut leanh::LeanObject,
    mut v___y_3518_: *mut leanh::LeanObject,
    mut v___y_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3522_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(v_ref_3515_, v_msg_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
    return v___x_3522_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___boxed(
    mut v_00_u03b1_3523_: *mut leanh::LeanObject,
    mut v_ref_3524_: *mut leanh::LeanObject,
    mut v_msg_3525_: *mut leanh::LeanObject,
    mut v___y_3526_: *mut leanh::LeanObject,
    mut v___y_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3531_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16(v_00_u03b1_3523_, v_ref_3524_, v_msg_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
    leanh::lean_dec(v___y_3529_);
    leanh::lean_dec_ref(v___y_3528_);
    leanh::lean_dec(v___y_3527_);
    leanh::lean_dec_ref(v___y_3526_);
    leanh::lean_dec(v_ref_3524_);
    return v_res_3531_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18(
    mut v_00_u03b1_3532_: *mut leanh::LeanObject,
    mut v_msg_3533_: *mut leanh::LeanObject,
    mut v___y_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3539_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(v_msg_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
    return v___x_3539_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___boxed(
    mut v_00_u03b1_3540_: *mut leanh::LeanObject,
    mut v_msg_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_3540_, v_msg_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
    leanh::lean_dec(v___y_3545_);
    leanh::lean_dec_ref(v___y_3544_);
    leanh::lean_dec(v___y_3543_);
    leanh::lean_dec_ref(v___y_3542_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0(
    mut v_env_3548_: *mut leanh::LeanObject,
    mut v_instances_3549_: u8,
    mut v_declName_3550_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3551_: u8 = 0;
    leanh::lean_inc(v_declName_3550_);
    leanh::lean_inc_ref(v_env_3548_);
    v___x_3551_ = lean_get_reducibility_status(v_env_3548_, v_declName_3550_);
    if v___x_3551_ == 1 {
        let mut v___x_3552_: u8 = 0;
        v___x_3552_ = l_Lean_Meta_isInstanceCore(v_env_3548_, v_declName_3550_);
        leanh::lean_dec(v_declName_3550_);
        if v___x_3552_ == 0 {
            if v_instances_3549_ == 0 {
                let mut v___x_3553_: u8 = 0;
                v___x_3553_ = 1;
                return v___x_3553_;
            } else {
                return v___x_3552_;
            }
        } else {
            return v_instances_3549_;
        }
    } else {
        let mut v___x_3554_: u8 = 0;
        leanh::lean_dec(v_declName_3550_);
        leanh::lean_dec_ref(v_env_3548_);
        v___x_3554_ = 0;
        return v___x_3554_;
    }
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0___boxed(
    mut v_env_3555_: *mut leanh::LeanObject,
    mut v_instances_3556_: *mut leanh::LeanObject,
    mut v_declName_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_instances_boxed_3558_: u8 = 0;
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_instances_boxed_3558_ = (leanh::lean_unbox(v_instances_3556_) as u8);
    v_res_3559_ = l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0(
        v_env_3555_,
        v_instances_boxed_3558_,
        v_declName_3557_,
    );
    v_r_3560_ = leanh::lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfolded(
    mut v_counters_3564_: *mut leanh::LeanObject,
    mut v_instances_3565_: u8,
    mut v_a_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
    mut v_a_3568_: *mut leanh::LeanObject,
    mut v_a_3569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3571_ = lean_st_ref_get(v_a_3569_);
    v_env_3572_ = leanh::lean_ctor_get(v___x_3571_, 0);
    leanh::lean_inc_ref(v_env_3572_);
    leanh::lean_dec(v___x_3571_);
    v___x_3573_ = leanh::lean_box((v_instances_3565_) as usize);
    v___f_3574_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3574_, 0, v_env_3572_);
    leanh::lean_closure_set(v___f_3574_, 1, v___x_3573_);
    v___x_3575_ = l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1;
    v___x_3576_ = l_Lean_Meta_mkDiagSummary(
        v___x_3575_,
        v_counters_3564_,
        v___f_3574_,
        v_a_3566_,
        v_a_3567_,
        v_a_3568_,
        v_a_3569_,
    );
    return v___x_3576_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfolded___boxed(
    mut v_counters_3577_: *mut leanh::LeanObject,
    mut v_instances_3578_: *mut leanh::LeanObject,
    mut v_a_3579_: *mut leanh::LeanObject,
    mut v_a_3580_: *mut leanh::LeanObject,
    mut v_a_3581_: *mut leanh::LeanObject,
    mut v_a_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_instances_boxed_3584_: u8 = 0;
    let mut v_res_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_instances_boxed_3584_ = (leanh::lean_unbox(v_instances_3578_) as u8);
    v_res_3585_ = l_Lean_Meta_mkDiagSummaryForUnfolded(
        v_counters_3577_,
        v_instances_boxed_3584_,
        v_a_3579_,
        v_a_3580_,
        v_a_3581_,
        v_a_3582_,
    );
    leanh::lean_dec(v_a_3582_);
    leanh::lean_dec_ref(v_a_3581_);
    leanh::lean_dec(v_a_3580_);
    leanh::lean_dec_ref(v_a_3579_);
    leanh::lean_dec_ref(v_counters_3577_);
    return v_res_3585_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lam__0(
    mut v_env_3586_: *mut leanh::LeanObject,
    mut v_declName_3587_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3588_: u8 = 0;
    v___x_3588_ = lean_get_reducibility_status(v_env_3586_, v_declName_3587_);
    if v___x_3588_ == 0 {
        let mut v___x_3589_: u8 = 0;
        v___x_3589_ = 1;
        return v___x_3589_;
    } else {
        let mut v___x_3590_: u8 = 0;
        v___x_3590_ = 0;
        return v___x_3590_;
    }
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lam__0___boxed(
    mut v_env_3591_: *mut leanh::LeanObject,
    mut v_declName_3592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3593_: u8 = 0;
    let mut v_r_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3593_ =
        l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lam__0(v_env_3591_, v_declName_3592_);
    v_r_3594_ = leanh::lean_box((v_res_3593_) as usize);
    return v_r_3594_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(
    mut v_counters_3595_: *mut leanh::LeanObject,
    mut v_a_3596_: *mut leanh::LeanObject,
    mut v_a_3597_: *mut leanh::LeanObject,
    mut v_a_3598_: *mut leanh::LeanObject,
    mut v_a_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3601_ = lean_st_ref_get(v_a_3599_);
    v_env_3602_ = leanh::lean_ctor_get(v___x_3601_, 0);
    leanh::lean_inc_ref(v_env_3602_);
    leanh::lean_dec(v___x_3601_);
    v___f_3603_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3603_, 0, v_env_3602_);
    v___x_3604_ = l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1;
    v___x_3605_ = l_Lean_Meta_mkDiagSummary(
        v___x_3604_,
        v_counters_3595_,
        v___f_3603_,
        v_a_3596_,
        v_a_3597_,
        v_a_3598_,
        v_a_3599_,
    );
    return v___x_3605_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___boxed(
    mut v_counters_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
    mut v_a_3609_: *mut leanh::LeanObject,
    mut v_a_3610_: *mut leanh::LeanObject,
    mut v_a_3611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ = l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(
        v_counters_3606_,
        v_a_3607_,
        v_a_3608_,
        v_a_3609_,
        v_a_3610_,
    );
    leanh::lean_dec(v_a_3610_);
    leanh::lean_dec_ref(v_a_3609_);
    leanh::lean_dec(v_a_3608_);
    leanh::lean_dec_ref(v_a_3607_);
    leanh::lean_dec_ref(v_counters_3606_);
    return v_res_3612_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0(
    mut v_x_3613_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3614_: u8 = 0;
    v___x_3614_ = 1;
    return v___x_3614_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0___boxed(
    mut v_x_3615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3616_: u8 = 0;
    let mut v_r_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0(v_x_3615_);
    leanh::lean_dec(v_x_3615_);
    v_r_3617_ = leanh::lean_box((v_res_3616_) as usize);
    return v_r_3617_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances(
    mut v_a_3622_: *mut leanh::LeanObject,
    mut v_a_3623_: *mut leanh::LeanObject,
    mut v_a_3624_: *mut leanh::LeanObject,
    mut v_a_3625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceCounter_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3627_ = lean_st_ref_get(v_a_3623_);
    v_diag_3628_ = leanh::lean_ctor_get(v___x_3627_, 4);
    leanh::lean_inc_ref(v_diag_3628_);
    leanh::lean_dec(v___x_3627_);
    v_instanceCounter_3629_ = leanh::lean_ctor_get(v_diag_3628_, 3);
    leanh::lean_inc_ref(v_instanceCounter_3629_);
    leanh::lean_dec_ref(v_diag_3628_);
    v___f_3630_ = l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__0;
    v___x_3631_ = l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2;
    v___x_3632_ = l_Lean_Meta_mkDiagSummary(
        v___x_3631_,
        v_instanceCounter_3629_,
        v___f_3630_,
        v_a_3622_,
        v_a_3623_,
        v_a_3624_,
        v_a_3625_,
    );
    leanh::lean_dec_ref(v_instanceCounter_3629_);
    return v___x_3632_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances___boxed(
    mut v_a_3633_: *mut leanh::LeanObject,
    mut v_a_3634_: *mut leanh::LeanObject,
    mut v_a_3635_: *mut leanh::LeanObject,
    mut v_a_3636_: *mut leanh::LeanObject,
    mut v_a_3637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3638_ =
        l_Lean_Meta_mkDiagSummaryForUsedInstances(v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
    leanh::lean_dec(v_a_3636_);
    leanh::lean_dec_ref(v_a_3635_);
    leanh::lean_dec(v_a_3634_);
    leanh::lean_dec_ref(v_a_3633_);
    return v_res_3638_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___redArg(
    mut v_x_3639_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3640_: u8 = 0;
    v___x_3640_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_3639_);
    return v___x_3640_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___redArg___boxed(
    mut v_x_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3642_: u8 = 0;
    let mut v_r_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3642_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___redArg(v_x_3641_);
    leanh::lean_dec_ref(v_x_3641_);
    v_r_3643_ = leanh::lean_box((v_res_3642_) as usize);
    return v_r_3643_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0(
    mut v_00_u03b2_3644_: *mut leanh::LeanObject,
    mut v_x_3645_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3646_: u8 = 0;
    v___x_3646_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_3645_);
    return v___x_3646_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___boxed(
    mut v_00_u03b2_3647_: *mut leanh::LeanObject,
    mut v_x_3648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3649_: u8 = 0;
    let mut v_r_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3649_ =
        l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0(
            v_00_u03b2_3647_,
            v_x_3648_,
        );
    leanh::lean_dec_ref(v_x_3648_);
    v_r_3650_ = leanh::lean_box((v_res_3649_) as usize);
    return v_r_3650_;
}
pub unsafe fn l_Lean_Meta_mkDiagSynthPendingFailure___lam__0(
    mut v___x_3651_: *mut leanh::LeanObject,
    mut v___x_3652_: u8,
    mut v_data_3653_: *mut leanh::LeanObject,
    mut v_x_3654_: *mut leanh::LeanObject,
    mut v_____s_3655_: *mut leanh::LeanObject,
    mut v___y_3656_: *mut leanh::LeanObject,
    mut v___y_3657_: *mut leanh::LeanObject,
    mut v___y_3658_: *mut leanh::LeanObject,
    mut v___y_3659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: f64 = 0.0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_3661_ = leanh::lean_ctor_get(v_x_3654_, 1);
    v___x_3662_ = l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2;
    v___x_3663_ = leanh::lean_box(0);
    v___x_3664_ = lean_float_of_nat(v___x_3651_);
    v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
    v___x_3666_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_3666_, 0, v___x_3662_);
    leanh::lean_ctor_set(v___x_3666_, 1, v___x_3663_);
    leanh::lean_ctor_set(v___x_3666_, 2, v___x_3665_);
    leanh::lean_ctor_set_float(
        v___x_3666_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_3664_,
    );
    leanh::lean_ctor_set_float(
        v___x_3666_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_3664_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3666_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_3652_,
    );
    leanh::lean_inc(v_snd_3661_);
    v___x_3667_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    leanh::lean_ctor_set(v___x_3667_, 1, v_snd_3661_);
    leanh::lean_ctor_set(v___x_3667_, 2, v_data_3653_);
    v_data_3668_ = lean_array_push(v_____s_3655_, v___x_3667_);
    v___x_3669_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3669_, 0, v_data_3668_);
    v___x_3670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3670_, 0, v___x_3669_);
    return v___x_3670_;
}
pub unsafe fn l_Lean_Meta_mkDiagSynthPendingFailure___lam__0___boxed(
    mut v___x_3671_: *mut leanh::LeanObject,
    mut v___x_3672_: *mut leanh::LeanObject,
    mut v_data_3673_: *mut leanh::LeanObject,
    mut v_x_3674_: *mut leanh::LeanObject,
    mut v_____s_3675_: *mut leanh::LeanObject,
    mut v___y_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2636__boxed_3681_: u8 = 0;
    let mut v_res_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2636__boxed_3681_ = (leanh::lean_unbox(v___x_3672_) as u8);
    v_res_3682_ = l_Lean_Meta_mkDiagSynthPendingFailure___lam__0(
        v___x_3671_,
        v___x_2636__boxed_3681_,
        v_data_3673_,
        v_x_3674_,
        v_____s_3675_,
        v___y_3676_,
        v___y_3677_,
        v___y_3678_,
        v___y_3679_,
    );
    leanh::lean_dec(v___y_3679_);
    leanh::lean_dec_ref(v___y_3678_);
    leanh::lean_dec(v___y_3677_);
    leanh::lean_dec_ref(v___y_3676_);
    leanh::lean_dec_ref(v_x_3674_);
    return v_res_3682_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___lam__0(
    mut v_f_3683_: *mut leanh::LeanObject,
    mut v_s_3684_: *mut leanh::LeanObject,
    mut v_a_3685_: *mut leanh::LeanObject,
    mut v_b_3686_: *mut leanh::LeanObject,
    mut v___y_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v_a_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3701_: u8 = 0;
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_a_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3692_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3692_, 0, v_a_3685_);
                leanh::lean_ctor_set(v___x_3692_, 1, v_b_3686_);
                leanh::lean_inc(v___y_3690_);
                leanh::lean_inc_ref(v___y_3689_);
                leanh::lean_inc(v___y_3688_);
                leanh::lean_inc_ref(v___y_3687_);
                v___x_3693_ = leanh::lean_apply_7(
                    v_f_3683_,
                    v___x_3692_,
                    v_s_3684_,
                    v___y_3687_,
                    v___y_3688_,
                    v___y_3689_,
                    v___y_3690_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3693_) == 0 {
                    v_a_3694_ = leanh::lean_ctor_get(v___x_3693_, 0);
                    v_isSharedCheck_3720_ = (!leanh::lean_is_exclusive(v___x_3693_)) as u8;
                    if v_isSharedCheck_3720_ == 0 {
                        v___x_3696_ = v___x_3693_;
                        v_isShared_3697_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3694_);
                        leanh::lean_dec(v___x_3693_);
                        v___x_3696_ = leanh::lean_box(0);
                        v_isShared_3697_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3721_ = leanh::lean_ctor_get(v___x_3693_, 0);
                    v_isSharedCheck_3728_ = (!leanh::lean_is_exclusive(v___x_3693_)) as u8;
                    if v_isSharedCheck_3728_ == 0 {
                        v___x_3723_ = v___x_3693_;
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3721_);
                        leanh::lean_dec(v___x_3693_);
                        v___x_3723_ = leanh::lean_box(0);
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3694_) == 0 {
                    v_a_3698_ = leanh::lean_ctor_get(v_a_3694_, 0);
                    v_isSharedCheck_3708_ = (!leanh::lean_is_exclusive(v_a_3694_)) as u8;
                    if v_isSharedCheck_3708_ == 0 {
                        v___x_3700_ = v_a_3694_;
                        v_isShared_3701_ = v_isSharedCheck_3708_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3698_);
                        leanh::lean_dec(v_a_3694_);
                        v___x_3700_ = leanh::lean_box(0);
                        v_isShared_3701_ = v_isSharedCheck_3708_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3709_ = leanh::lean_ctor_get(v_a_3694_, 0);
                    v_isSharedCheck_3719_ = (!leanh::lean_is_exclusive(v_a_3694_)) as u8;
                    if v_isSharedCheck_3719_ == 0 {
                        v___x_3711_ = v_a_3694_;
                        v_isShared_3712_ = v_isSharedCheck_3719_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3709_);
                        leanh::lean_dec(v_a_3694_);
                        v___x_3711_ = leanh::lean_box(0);
                        v_isShared_3712_ = v_isSharedCheck_3719_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3701_ == 0 {
                    v___x_3703_ = v___x_3700_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3698_);
                    v___x_3703_ = v_reuseFailAlloc_3707_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3697_ == 0 {
                    leanh::lean_ctor_set(v___x_3696_, 0, v___x_3703_);
                    v___x_3705_ = v___x_3696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3706_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
                    v___x_3705_ = v_reuseFailAlloc_3706_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3705_;
            }
            5 => {
                if v_isShared_3712_ == 0 {
                    v___x_3714_ = v___x_3711_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3709_);
                    v___x_3714_ = v_reuseFailAlloc_3718_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3697_ == 0 {
                    leanh::lean_ctor_set(v___x_3696_, 0, v___x_3714_);
                    v___x_3716_ = v___x_3696_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
                    v___x_3716_ = v_reuseFailAlloc_3717_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3716_;
            }
            8 => {
                if v_isShared_3724_ == 0 {
                    v___x_3726_ = v___x_3723_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___lam__0___boxed(
    mut v_f_3729_: *mut leanh::LeanObject,
    mut v_s_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_b_3732_: *mut leanh::LeanObject,
    mut v___y_3733_: *mut leanh::LeanObject,
    mut v___y_3734_: *mut leanh::LeanObject,
    mut v___y_3735_: *mut leanh::LeanObject,
    mut v___y_3736_: *mut leanh::LeanObject,
    mut v___y_3737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3738_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___lam__0(v_f_3729_, v_s_3730_, v_a_3731_, v_b_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
    leanh::lean_dec(v___y_3736_);
    leanh::lean_dec_ref(v___y_3735_);
    leanh::lean_dec(v___y_3734_);
    leanh::lean_dec_ref(v___y_3733_);
    return v_res_3738_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_f_3739_: *mut leanh::LeanObject,
    mut v_keys_3740_: *mut leanh::LeanObject,
    mut v_vals_3741_: *mut leanh::LeanObject,
    mut v_i_3742_: *mut leanh::LeanObject,
    mut v_acc_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3749_ = lean_array_get_size(v_keys_3740_);
                v___x_3750_ = lean_nat_dec_lt(v_i_3742_, v___x_3749_);
                if v___x_3750_ == 0 {
                    leanh::lean_dec(v_i_3742_);
                    leanh::lean_dec_ref(v_f_3739_);
                    v___x_3751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3751_, 0, v_acc_3743_);
                    v___x_3752_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3752_, 0, v___x_3751_);
                    return v___x_3752_;
                } else {
                    v_k_3753_ = lean_array_fget_borrowed(v_keys_3740_, v_i_3742_);
                    v_v_3754_ = lean_array_fget_borrowed(v_vals_3741_, v_i_3742_);
                    leanh::lean_inc_ref(v_f_3739_);
                    leanh::lean_inc(v___y_3747_);
                    leanh::lean_inc_ref(v___y_3746_);
                    leanh::lean_inc(v___y_3745_);
                    leanh::lean_inc_ref(v___y_3744_);
                    leanh::lean_inc(v_v_3754_);
                    leanh::lean_inc(v_k_3753_);
                    v___x_3755_ = leanh::lean_apply_8(
                        v_f_3739_,
                        v_acc_3743_,
                        v_k_3753_,
                        v_v_3754_,
                        v___y_3744_,
                        v___y_3745_,
                        v___y_3746_,
                        v___y_3747_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3755_) == 0 {
                        v_a_3756_ = leanh::lean_ctor_get(v___x_3755_, 0);
                        leanh::lean_inc(v_a_3756_);
                        if leanh::lean_obj_tag(v_a_3756_) == 0 {
                            leanh::lean_dec_ref_known(v_a_3756_, 1);
                            leanh::lean_dec(v_i_3742_);
                            leanh::lean_dec_ref(v_f_3739_);
                            return v___x_3755_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_3755_, 1);
                            v_a_3757_ = leanh::lean_ctor_get(v_a_3756_, 0);
                            leanh::lean_inc(v_a_3757_);
                            leanh::lean_dec_ref_known(v_a_3756_, 1);
                            v___x_3758_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3759_ = lean_nat_add(v_i_3742_, v___x_3758_);
                            leanh::lean_dec(v_i_3742_);
                            v_i_3742_ = v___x_3759_;
                            v_acc_3743_ = v_a_3757_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_i_3742_);
                        leanh::lean_dec_ref(v_f_3739_);
                        return v___x_3755_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_f_3761_: *mut leanh::LeanObject,
    mut v_keys_3762_: *mut leanh::LeanObject,
    mut v_vals_3763_: *mut leanh::LeanObject,
    mut v_i_3764_: *mut leanh::LeanObject,
    mut v_acc_3765_: *mut leanh::LeanObject,
    mut v___y_3766_: *mut leanh::LeanObject,
    mut v___y_3767_: *mut leanh::LeanObject,
    mut v___y_3768_: *mut leanh::LeanObject,
    mut v___y_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3761_, v_keys_3762_, v_vals_3763_, v_i_3764_, v_acc_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
    leanh::lean_dec(v___y_3769_);
    leanh::lean_dec_ref(v___y_3768_);
    leanh::lean_dec(v___y_3767_);
    leanh::lean_dec_ref(v___y_3766_);
    leanh::lean_dec_ref(v_vals_3763_);
    leanh::lean_dec_ref(v_keys_3762_);
    return v_res_3771_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(
    mut v_f_3772_: *mut leanh::LeanObject,
    mut v_x_3773_: *mut leanh::LeanObject,
    mut v_x_3774_: *mut leanh::LeanObject,
    mut v___y_3775_: *mut leanh::LeanObject,
    mut v___y_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: usize = 0;
    let mut v___x_3800_: usize = 0;
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_ks_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3773_) == 0 {
                    v_es_3780_ = leanh::lean_ctor_get(v_x_3773_, 0);
                    v_isSharedCheck_3802_ = (!leanh::lean_is_exclusive(v_x_3773_)) as u8;
                    if v_isSharedCheck_3802_ == 0 {
                        v___x_3782_ = v_x_3773_;
                        v_isShared_3783_ = v_isSharedCheck_3802_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_3780_);
                        leanh::lean_dec(v_x_3773_);
                        v___x_3782_ = leanh::lean_box(0);
                        v_isShared_3783_ = v_isSharedCheck_3802_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_3803_ = leanh::lean_ctor_get(v_x_3773_, 0);
                    leanh::lean_inc_ref(v_ks_3803_);
                    v_vs_3804_ = leanh::lean_ctor_get(v_x_3773_, 1);
                    leanh::lean_inc_ref(v_vs_3804_);
                    leanh::lean_dec_ref_known(v_x_3773_, 2);
                    v___x_3805_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3772_, v_ks_3803_, v_vs_3804_, v___x_3805_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
                    leanh::lean_dec_ref(v_vs_3804_);
                    leanh::lean_dec_ref(v_ks_3803_);
                    return v___x_3806_;
                }
            }
            1 => {
                v___x_3784_ = leanh::lean_unsigned_to_nat(0);
                v___x_3785_ = lean_array_get_size(v_es_3780_);
                v___x_3786_ = lean_nat_dec_lt(v___x_3784_, v___x_3785_);
                if v___x_3786_ == 0 {
                    leanh::lean_dec_ref(v_es_3780_);
                    leanh::lean_dec_ref(v_f_3772_);
                    if v_isShared_3783_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3782_, 1);
                        leanh::lean_ctor_set(v___x_3782_, 0, v_x_3774_);
                        v___x_3788_ = v___x_3782_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3790_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_x_3774_);
                        v___x_3788_ = v_reuseFailAlloc_3790_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3791_ = lean_nat_dec_le(v___x_3785_, v___x_3785_);
                    if v___x_3791_ == 0 {
                        if v___x_3786_ == 0 {
                            leanh::lean_dec_ref(v_es_3780_);
                            leanh::lean_dec_ref(v_f_3772_);
                            if v_isShared_3783_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_3782_, 1);
                                leanh::lean_ctor_set(v___x_3782_, 0, v_x_3774_);
                                v___x_3793_ = v___x_3782_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3795_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_x_3774_);
                                v___x_3793_ = v_reuseFailAlloc_3795_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3782_);
                            v___x_3796_ = 0usize;
                            v___x_3797_ = lean_usize_of_nat(v___x_3785_);
                            v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3772_, v_es_3780_, v___x_3796_, v___x_3797_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
                            leanh::lean_dec_ref(v_es_3780_);
                            return v___x_3798_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3782_);
                        v___x_3799_ = 0usize;
                        v___x_3800_ = lean_usize_of_nat(v___x_3785_);
                        v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3772_, v_es_3780_, v___x_3799_, v___x_3800_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
                        leanh::lean_dec_ref(v_es_3780_);
                        return v___x_3801_;
                    }
                }
            }
            2 => {
                v___x_3789_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3789_, 0, v___x_3788_);
                return v___x_3789_;
            }
            3 => {
                v___x_3794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3794_, 0, v___x_3793_);
                return v___x_3794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_f_3807_: *mut leanh::LeanObject,
    mut v_as_3808_: *mut leanh::LeanObject,
    mut v_i_3809_: usize,
    mut v_stop_3810_: usize,
    mut v_b_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
    mut v___y_3813_: *mut leanh::LeanObject,
    mut v___y_3814_: *mut leanh::LeanObject,
    mut v___y_3815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: usize = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___y_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: u8 = 0;
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3826_ = lean_usize_dec_eq(v_i_3809_, v_stop_3810_);
                if v___x_3826_ == 0 {
                    v___x_3827_ = lean_array_uget_borrowed(v_as_3808_, v_i_3809_);
                    match leanh::lean_obj_tag(v___x_3827_) {
                        0 => {
                            v_key_3828_ = leanh::lean_ctor_get(v___x_3827_, 0);
                            v_val_3829_ = leanh::lean_ctor_get(v___x_3827_, 1);
                            leanh::lean_inc_ref(v_f_3807_);
                            leanh::lean_inc(v___y_3815_);
                            leanh::lean_inc_ref(v___y_3814_);
                            leanh::lean_inc(v___y_3813_);
                            leanh::lean_inc_ref(v___y_3812_);
                            leanh::lean_inc(v_val_3829_);
                            leanh::lean_inc(v_key_3828_);
                            v___x_3830_ = leanh::lean_apply_8(
                                v_f_3807_,
                                v_b_3811_,
                                v_key_3828_,
                                v_val_3829_,
                                v___y_3812_,
                                v___y_3813_,
                                v___y_3814_,
                                v___y_3815_,
                                leanh::lean_box(0),
                            );
                            v___y_3823_ = v___x_3830_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_3831_ = leanh::lean_ctor_get(v___x_3827_, 0);
                            leanh::lean_inc(v_node_3831_);
                            leanh::lean_inc_ref(v_f_3807_);
                            v___x_3832_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_3807_, v_node_3831_, v_b_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
                            v___y_3823_ = v___x_3832_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_3818_ = v_b_3811_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_3807_);
                    v___x_3833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3833_, 0, v_b_3811_);
                    v___x_3834_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3834_, 0, v___x_3833_);
                    return v___x_3834_;
                }
            }
            1 => {
                v___x_3819_ = 1usize;
                v___x_3820_ = lean_usize_add(v_i_3809_, v___x_3819_);
                v_i_3809_ = v___x_3820_;
                v_b_3811_ = v_a_3818_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3823_) == 0 {
                    v_a_3824_ = leanh::lean_ctor_get(v___y_3823_, 0);
                    if leanh::lean_obj_tag(v_a_3824_) == 0 {
                        leanh::lean_dec_ref(v_f_3807_);
                        return v___y_3823_;
                    } else {
                        leanh::lean_inc_ref(v_a_3824_);
                        leanh::lean_dec_ref_known(v___y_3823_, 1);
                        v_a_3825_ = leanh::lean_ctor_get(v_a_3824_, 0);
                        leanh::lean_inc(v_a_3825_);
                        leanh::lean_dec_ref_known(v_a_3824_, 1);
                        v_a_3818_ = v_a_3825_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_3807_);
                    return v___y_3823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_f_3835_: *mut leanh::LeanObject,
    mut v_as_3836_: *mut leanh::LeanObject,
    mut v_i_3837_: *mut leanh::LeanObject,
    mut v_stop_3838_: *mut leanh::LeanObject,
    mut v_b_3839_: *mut leanh::LeanObject,
    mut v___y_3840_: *mut leanh::LeanObject,
    mut v___y_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
    mut v___y_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3845_: usize = 0;
    let mut v_stop_boxed_3846_: usize = 0;
    let mut v_res_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3845_ = leanh::lean_unbox_usize(v_i_3837_);
    leanh::lean_dec(v_i_3837_);
    v_stop_boxed_3846_ = leanh::lean_unbox_usize(v_stop_3838_);
    leanh::lean_dec(v_stop_3838_);
    v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3835_, v_as_3836_, v_i_boxed_3845_, v_stop_boxed_3846_, v_b_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
    leanh::lean_dec(v___y_3843_);
    leanh::lean_dec_ref(v___y_3842_);
    leanh::lean_dec(v___y_3841_);
    leanh::lean_dec_ref(v___y_3840_);
    leanh::lean_dec_ref(v_as_3836_);
    return v_res_3847_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_3848_: *mut leanh::LeanObject,
    mut v_x_3849_: *mut leanh::LeanObject,
    mut v_x_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
    mut v___y_3853_: *mut leanh::LeanObject,
    mut v___y_3854_: *mut leanh::LeanObject,
    mut v___y_3855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3856_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_3848_, v_x_3849_, v_x_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
    leanh::lean_dec(v___y_3854_);
    leanh::lean_dec_ref(v___y_3853_);
    leanh::lean_dec(v___y_3852_);
    leanh::lean_dec_ref(v___y_3851_);
    return v_res_3856_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(
    mut v_map_3857_: *mut leanh::LeanObject,
    mut v_init_3858_: *mut leanh::LeanObject,
    mut v_f_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
    mut v___y_3862_: *mut leanh::LeanObject,
    mut v___y_3863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v_a_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3875_: u8 = 0;
    let mut v_a_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3865_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                leanh::lean_closure_set(v___f_3865_, 0, v_f_3859_);
                leanh::lean_inc_ref(v_map_3857_);
                v___x_3866_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v___f_3865_, v_map_3857_, v_init_3858_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
                if leanh::lean_obj_tag(v___x_3866_) == 0 {
                    v_a_3867_ = leanh::lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3875_ = (!leanh::lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3875_ == 0 {
                        v___x_3869_ = v___x_3866_;
                        v_isShared_3870_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3867_);
                        leanh::lean_dec(v___x_3866_);
                        v___x_3869_ = leanh::lean_box(0);
                        v_isShared_3870_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3876_ = leanh::lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3883_ = (!leanh::lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3883_ == 0 {
                        v___x_3878_ = v___x_3866_;
                        v_isShared_3879_ = v_isSharedCheck_3883_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3876_);
                        leanh::lean_dec(v___x_3866_);
                        v___x_3878_ = leanh::lean_box(0);
                        v_isShared_3879_ = v_isSharedCheck_3883_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3871_ = leanh::lean_ctor_get(v_a_3867_, 0);
                leanh::lean_inc(v_a_3871_);
                leanh::lean_dec(v_a_3867_);
                if v_isShared_3870_ == 0 {
                    leanh::lean_ctor_set(v___x_3869_, 0, v_a_3871_);
                    v___x_3873_ = v___x_3869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3871_);
                    v___x_3873_ = v_reuseFailAlloc_3874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3873_;
            }
            3 => {
                if v_isShared_3879_ == 0 {
                    v___x_3881_ = v___x_3878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
                    v___x_3881_ = v_reuseFailAlloc_3882_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___boxed(
    mut v_map_3884_: *mut leanh::LeanObject,
    mut v_init_3885_: *mut leanh::LeanObject,
    mut v_f_3886_: *mut leanh::LeanObject,
    mut v___y_3887_: *mut leanh::LeanObject,
    mut v___y_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3892_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(v_map_3884_, v_init_3885_, v_f_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
    leanh::lean_dec(v___y_3890_);
    leanh::lean_dec_ref(v___y_3889_);
    leanh::lean_dec(v___y_3888_);
    leanh::lean_dec_ref(v___y_3887_);
    leanh::lean_dec_ref(v_map_3884_);
    return v_res_3892_;
}
pub unsafe fn l_Lean_Meta_mkDiagSynthPendingFailure(
    mut v_failures_3898_: *mut leanh::LeanObject,
    mut v_a_3899_: *mut leanh::LeanObject,
    mut v_a_3900_: *mut leanh::LeanObject,
    mut v_a_3901_: *mut leanh::LeanObject,
    mut v_a_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3917_: u8 = 0;
    let mut v_a_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3921_: u8 = 0;
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3904_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_failures_3898_);
                if v___x_3904_ == 0 {
                    v___x_3905_ = leanh::lean_unsigned_to_nat(0);
                    v_data_3906_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__0;
                    v___f_3907_ = l_Lean_Meta_mkDiagSynthPendingFailure___closed__0;
                    v___x_3908_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(v_failures_3898_, v_data_3906_, v___f_3907_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                    if leanh::lean_obj_tag(v___x_3908_) == 0 {
                        v_a_3909_ = leanh::lean_ctor_get(v___x_3908_, 0);
                        v_isSharedCheck_3917_ =
                            (!leanh::lean_is_exclusive(v___x_3908_)) as u8;
                        if v_isSharedCheck_3917_ == 0 {
                            v___x_3911_ = v___x_3908_;
                            v_isShared_3912_ = v_isSharedCheck_3917_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3909_);
                            leanh::lean_dec(v___x_3908_);
                            v___x_3911_ = leanh::lean_box(0);
                            v_isShared_3912_ = v_isSharedCheck_3917_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3918_ = leanh::lean_ctor_get(v___x_3908_, 0);
                        v_isSharedCheck_3925_ =
                            (!leanh::lean_is_exclusive(v___x_3908_)) as u8;
                        if v_isSharedCheck_3925_ == 0 {
                            v___x_3920_ = v___x_3908_;
                            v_isShared_3921_ = v_isSharedCheck_3925_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3918_);
                            leanh::lean_dec(v___x_3908_);
                            v___x_3920_ = leanh::lean_box(0);
                            v_isShared_3921_ = v_isSharedCheck_3925_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3926_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__1;
                    v___x_3927_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3927_, 0, v___x_3926_);
                    return v___x_3927_;
                }
            }
            1 => {
                v___x_3913_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3913_, 0, v_a_3909_);
                leanh::lean_ctor_set(v___x_3913_, 1, v___x_3905_);
                if v_isShared_3912_ == 0 {
                    leanh::lean_ctor_set(v___x_3911_, 0, v___x_3913_);
                    v___x_3915_ = v___x_3911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
                    v___x_3915_ = v_reuseFailAlloc_3916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3915_;
            }
            3 => {
                if v_isShared_3921_ == 0 {
                    v___x_3923_ = v___x_3920_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
                    v___x_3923_ = v_reuseFailAlloc_3924_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkDiagSynthPendingFailure___boxed(
    mut v_failures_3928_: *mut leanh::LeanObject,
    mut v_a_3929_: *mut leanh::LeanObject,
    mut v_a_3930_: *mut leanh::LeanObject,
    mut v_a_3931_: *mut leanh::LeanObject,
    mut v_a_3932_: *mut leanh::LeanObject,
    mut v_a_3933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3934_ = l_Lean_Meta_mkDiagSynthPendingFailure(
        v_failures_3928_,
        v_a_3929_,
        v_a_3930_,
        v_a_3931_,
        v_a_3932_,
    );
    leanh::lean_dec(v_a_3932_);
    leanh::lean_dec_ref(v_a_3931_);
    leanh::lean_dec(v_a_3930_);
    leanh::lean_dec_ref(v_a_3929_);
    leanh::lean_dec_ref(v_failures_3928_);
    return v_res_3934_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1(
    mut v_00_u03c3_3935_: *mut leanh::LeanObject,
    mut v_00_u03b2_3936_: *mut leanh::LeanObject,
    mut v_map_3937_: *mut leanh::LeanObject,
    mut v_init_3938_: *mut leanh::LeanObject,
    mut v_f_3939_: *mut leanh::LeanObject,
    mut v___y_3940_: *mut leanh::LeanObject,
    mut v___y_3941_: *mut leanh::LeanObject,
    mut v___y_3942_: *mut leanh::LeanObject,
    mut v___y_3943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(v_map_3937_, v_init_3938_, v_f_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
    return v___x_3945_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___boxed(
    mut v_00_u03c3_3946_: *mut leanh::LeanObject,
    mut v_00_u03b2_3947_: *mut leanh::LeanObject,
    mut v_map_3948_: *mut leanh::LeanObject,
    mut v_init_3949_: *mut leanh::LeanObject,
    mut v_f_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3956_ =
        l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1(
            v_00_u03c3_3946_,
            v_00_u03b2_3947_,
            v_map_3948_,
            v_init_3949_,
            v_f_3950_,
            v___y_3951_,
            v___y_3952_,
            v___y_3953_,
            v___y_3954_,
        );
    leanh::lean_dec(v___y_3954_);
    leanh::lean_dec_ref(v___y_3953_);
    leanh::lean_dec(v___y_3952_);
    leanh::lean_dec_ref(v___y_3951_);
    leanh::lean_dec_ref(v_map_3948_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___redArg(
    mut v_map_3957_: *mut leanh::LeanObject,
    mut v_f_3958_: *mut leanh::LeanObject,
    mut v_init_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
    mut v___y_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3965_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_3958_, v_map_3957_, v_init_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
    return v___x_3965_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___redArg___boxed(
    mut v_map_3966_: *mut leanh::LeanObject,
    mut v_f_3967_: *mut leanh::LeanObject,
    mut v_init_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
    mut v___y_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___redArg(v_map_3966_, v_f_3967_, v_init_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
    leanh::lean_dec(v___y_3972_);
    leanh::lean_dec_ref(v___y_3971_);
    leanh::lean_dec(v___y_3970_);
    leanh::lean_dec_ref(v___y_3969_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1(
    mut v_00_u03c3_3975_: *mut leanh::LeanObject,
    mut v_00_u03c3_3976_: *mut leanh::LeanObject,
    mut v_00_u03b2_3977_: *mut leanh::LeanObject,
    mut v_map_3978_: *mut leanh::LeanObject,
    mut v_f_3979_: *mut leanh::LeanObject,
    mut v_init_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3986_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_3979_, v_map_3978_, v_init_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
    return v___x_3986_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___boxed(
    mut v_00_u03c3_3987_: *mut leanh::LeanObject,
    mut v_00_u03c3_3988_: *mut leanh::LeanObject,
    mut v_00_u03b2_3989_: *mut leanh::LeanObject,
    mut v_map_3990_: *mut leanh::LeanObject,
    mut v_f_3991_: *mut leanh::LeanObject,
    mut v_init_3992_: *mut leanh::LeanObject,
    mut v___y_3993_: *mut leanh::LeanObject,
    mut v___y_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
    mut v___y_3996_: *mut leanh::LeanObject,
    mut v___y_3997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1(v_00_u03c3_3987_, v_00_u03c3_3988_, v_00_u03b2_3989_, v_map_3990_, v_f_3991_, v_init_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
    leanh::lean_dec(v___y_3996_);
    leanh::lean_dec_ref(v___y_3995_);
    leanh::lean_dec(v___y_3994_);
    leanh::lean_dec_ref(v___y_3993_);
    return v_res_3998_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2(
    mut v_00_u03c3_3999_: *mut leanh::LeanObject,
    mut v_00_u03c3_4000_: *mut leanh::LeanObject,
    mut v_00_u03b1_4001_: *mut leanh::LeanObject,
    mut v_00_u03b2_4002_: *mut leanh::LeanObject,
    mut v_f_4003_: *mut leanh::LeanObject,
    mut v_x_4004_: *mut leanh::LeanObject,
    mut v_x_4005_: *mut leanh::LeanObject,
    mut v___y_4006_: *mut leanh::LeanObject,
    mut v___y_4007_: *mut leanh::LeanObject,
    mut v___y_4008_: *mut leanh::LeanObject,
    mut v___y_4009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4011_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_4003_, v_x_4004_, v_x_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
    return v___x_4011_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03c3_4012_: *mut leanh::LeanObject,
    mut v_00_u03c3_4013_: *mut leanh::LeanObject,
    mut v_00_u03b1_4014_: *mut leanh::LeanObject,
    mut v_00_u03b2_4015_: *mut leanh::LeanObject,
    mut v_f_4016_: *mut leanh::LeanObject,
    mut v_x_4017_: *mut leanh::LeanObject,
    mut v_x_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
    mut v___y_4023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4024_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2(v_00_u03c3_4012_, v_00_u03c3_4013_, v_00_u03b1_4014_, v_00_u03b2_4015_, v_f_4016_, v_x_4017_, v_x_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
    leanh::lean_dec(v___y_4022_);
    leanh::lean_dec_ref(v___y_4021_);
    leanh::lean_dec(v___y_4020_);
    leanh::lean_dec_ref(v___y_4019_);
    return v_res_4024_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_4025_: *mut leanh::LeanObject,
    mut v_00_u03b2_4026_: *mut leanh::LeanObject,
    mut v_00_u03c3_4027_: *mut leanh::LeanObject,
    mut v_00_u03c3_4028_: *mut leanh::LeanObject,
    mut v_f_4029_: *mut leanh::LeanObject,
    mut v_as_4030_: *mut leanh::LeanObject,
    mut v_i_4031_: usize,
    mut v_stop_4032_: usize,
    mut v_b_4033_: *mut leanh::LeanObject,
    mut v___y_4034_: *mut leanh::LeanObject,
    mut v___y_4035_: *mut leanh::LeanObject,
    mut v___y_4036_: *mut leanh::LeanObject,
    mut v___y_4037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4029_, v_as_4030_, v_i_4031_, v_stop_4032_, v_b_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
    return v___x_4039_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_4040_: *mut leanh::LeanObject,
    mut v_00_u03b2_4041_: *mut leanh::LeanObject,
    mut v_00_u03c3_4042_: *mut leanh::LeanObject,
    mut v_00_u03c3_4043_: *mut leanh::LeanObject,
    mut v_f_4044_: *mut leanh::LeanObject,
    mut v_as_4045_: *mut leanh::LeanObject,
    mut v_i_4046_: *mut leanh::LeanObject,
    mut v_stop_4047_: *mut leanh::LeanObject,
    mut v_b_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
    mut v___y_4053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4054_: usize = 0;
    let mut v_stop_boxed_4055_: usize = 0;
    let mut v_res_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4054_ = leanh::lean_unbox_usize(v_i_4046_);
    leanh::lean_dec(v_i_4046_);
    v_stop_boxed_4055_ = leanh::lean_unbox_usize(v_stop_4047_);
    leanh::lean_dec(v_stop_4047_);
    v_res_4056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4040_, v_00_u03b2_4041_, v_00_u03c3_4042_, v_00_u03c3_4043_, v_f_4044_, v_as_4045_, v_i_boxed_4054_, v_stop_boxed_4055_, v_b_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
    leanh::lean_dec(v___y_4052_);
    leanh::lean_dec_ref(v___y_4051_);
    leanh::lean_dec(v___y_4050_);
    leanh::lean_dec_ref(v___y_4049_);
    leanh::lean_dec_ref(v_as_4045_);
    return v_res_4056_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03c3_4057_: *mut leanh::LeanObject,
    mut v_00_u03c3_4058_: *mut leanh::LeanObject,
    mut v_00_u03b1_4059_: *mut leanh::LeanObject,
    mut v_00_u03b2_4060_: *mut leanh::LeanObject,
    mut v_f_4061_: *mut leanh::LeanObject,
    mut v_keys_4062_: *mut leanh::LeanObject,
    mut v_vals_4063_: *mut leanh::LeanObject,
    mut v_heq_4064_: *mut leanh::LeanObject,
    mut v_i_4065_: *mut leanh::LeanObject,
    mut v_acc_4066_: *mut leanh::LeanObject,
    mut v___y_4067_: *mut leanh::LeanObject,
    mut v___y_4068_: *mut leanh::LeanObject,
    mut v___y_4069_: *mut leanh::LeanObject,
    mut v___y_4070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4072_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4061_, v_keys_4062_, v_vals_4063_, v_i_4065_, v_acc_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
    return v___x_4072_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03c3_4073_: *mut leanh::LeanObject,
    mut v_00_u03c3_4074_: *mut leanh::LeanObject,
    mut v_00_u03b1_4075_: *mut leanh::LeanObject,
    mut v_00_u03b2_4076_: *mut leanh::LeanObject,
    mut v_f_4077_: *mut leanh::LeanObject,
    mut v_keys_4078_: *mut leanh::LeanObject,
    mut v_vals_4079_: *mut leanh::LeanObject,
    mut v_heq_4080_: *mut leanh::LeanObject,
    mut v_i_4081_: *mut leanh::LeanObject,
    mut v_acc_4082_: *mut leanh::LeanObject,
    mut v___y_4083_: *mut leanh::LeanObject,
    mut v___y_4084_: *mut leanh::LeanObject,
    mut v___y_4085_: *mut leanh::LeanObject,
    mut v___y_4086_: *mut leanh::LeanObject,
    mut v___y_4087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4088_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4073_, v_00_u03c3_4074_, v_00_u03b1_4075_, v_00_u03b2_4076_, v_f_4077_, v_keys_4078_, v_vals_4079_, v_heq_4080_, v_i_4081_, v_acc_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
    leanh::lean_dec(v___y_4086_);
    leanh::lean_dec_ref(v___y_4085_);
    leanh::lean_dec(v___y_4084_);
    leanh::lean_dec_ref(v___y_4083_);
    leanh::lean_dec_ref(v_vals_4079_);
    leanh::lean_dec_ref(v_keys_4078_);
    return v_res_4088_;
}
pub unsafe fn l_Lean_Meta_appendSection(
    mut v_m_4092_: *mut leanh::LeanObject,
    mut v_cls_4093_: *mut leanh::LeanObject,
    mut v_header_4094_: *mut leanh::LeanObject,
    mut v_s_4095_: *mut leanh::LeanObject,
    mut v_resultSummary_4096_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: u8 = 0;
    let mut v___y_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: f64 = 0.0;
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_max_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4097_ = l_Lean_Meta_DiagSummary_isEmpty(v_s_4095_);
                if v___x_4097_ == 0 {
                    v___x_4098_ = 1;
                    if v_resultSummary_4096_ == 0 {
                        v___y_4100_ = v_header_4094_;
                        state = 1;
                        continue;
                    } else {
                        v_data_4110_ = leanh::lean_ctor_get(v_s_4095_, 0);
                        v_max_4111_ = leanh::lean_ctor_get(v_s_4095_, 1);
                        v___x_4112_ = l_Lean_Meta_appendSection___closed__0;
                        v___x_4113_ = lean_string_append(v_header_4094_, v___x_4112_);
                        leanh::lean_inc(v_max_4111_);
                        v___x_4114_ = l_Nat_reprFast(v_max_4111_);
                        v___x_4115_ = lean_string_append(v___x_4113_, v___x_4114_);
                        leanh::lean_dec_ref(v___x_4114_);
                        v___x_4116_ = l_Lean_Meta_appendSection___closed__1;
                        v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
                        v___x_4118_ = lean_array_get_size(v_data_4110_);
                        v___x_4119_ = l_Nat_reprFast(v___x_4118_);
                        v___x_4120_ = lean_string_append(v___x_4117_, v___x_4119_);
                        leanh::lean_dec_ref(v___x_4119_);
                        v___x_4121_ = l_Lean_Meta_appendSection___closed__2;
                        v___x_4122_ = lean_string_append(v___x_4120_, v___x_4121_);
                        v___y_4100_ = v___x_4122_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_s_4095_);
                    leanh::lean_dec_ref(v_header_4094_);
                    leanh::lean_dec(v_cls_4093_);
                    return v_m_4092_;
                }
            }
            1 => {
                v___x_4101_ = leanh::lean_box(0);
                v___x_4102_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0);
                v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
                v___x_4104_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4104_, 0, v_cls_4093_);
                leanh::lean_ctor_set(v___x_4104_, 1, v___x_4101_);
                leanh::lean_ctor_set(v___x_4104_, 2, v___x_4103_);
                leanh::lean_ctor_set_float(
                    v___x_4104_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4102_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4104_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4102_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4104_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4098_,
                );
                v_data_4105_ = leanh::lean_ctor_get(v_s_4095_, 0);
                leanh::lean_inc_ref(v_data_4105_);
                leanh::lean_dec_ref(v_s_4095_);
                v___x_4106_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4106_, 0, v___y_4100_);
                v___x_4107_ = l_Lean_MessageData_ofFormat(v___x_4106_);
                v___x_4108_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4108_, 0, v___x_4104_);
                leanh::lean_ctor_set(v___x_4108_, 1, v___x_4107_);
                leanh::lean_ctor_set(v___x_4108_, 2, v_data_4105_);
                v___x_4109_ = lean_array_push(v_m_4092_, v___x_4108_);
                return v___x_4109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_appendSection___boxed(
    mut v_m_4123_: *mut leanh::LeanObject,
    mut v_cls_4124_: *mut leanh::LeanObject,
    mut v_header_4125_: *mut leanh::LeanObject,
    mut v_s_4126_: *mut leanh::LeanObject,
    mut v_resultSummary_4127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_resultSummary_boxed_4128_: u8 = 0;
    let mut v_res_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_resultSummary_boxed_4128_ = (leanh::lean_unbox(v_resultSummary_4127_) as u8);
    v_res_4129_ = l_Lean_Meta_appendSection(
        v_m_4123_,
        v_cls_4124_,
        v_header_4125_,
        v_s_4126_,
        v_resultSummary_boxed_4128_,
    );
    return v_res_4129_;
}
pub unsafe fn l_Lean_Meta_reportDiag___lam__0(
    mut v_a_4130_: u8,
    mut v_x_4131_: *mut leanh::LeanObject,
) -> u8 {
    return v_a_4130_;
}
pub unsafe fn l_Lean_Meta_reportDiag___lam__0___boxed(
    mut v_a_4132_: *mut leanh::LeanObject,
    mut v_x_4133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_13695__boxed_4134_: u8 = 0;
    let mut v_res_4135_: u8 = 0;
    let mut v_r_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_13695__boxed_4134_ = (leanh::lean_unbox(v_a_4132_) as u8);
    v_res_4135_ = l_Lean_Meta_reportDiag___lam__0(v_a_13695__boxed_4134_, v_x_4133_);
    leanh::lean_dec(v_x_4133_);
    v_r_4136_ = leanh::lean_box((v_res_4135_) as usize);
    return v_r_4136_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0(
    mut v___y_4145_: u8,
    mut v_suppressElabErrors_4146_: u8,
    mut v_x_4147_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4147_) == 1 {
        let mut v_pre_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_4148_ = leanh::lean_ctor_get(v_x_4147_, 0);
        match leanh::lean_obj_tag(v_pre_4148_) {
            1 => {
                let mut v_pre_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_4149_ = leanh::lean_ctor_get(v_pre_4148_, 0);
                match leanh::lean_obj_tag(v_pre_4149_) {
                    0 => {
                        let mut v_str_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4153_: u8 = 0;
                        v_str_4150_ = leanh::lean_ctor_get(v_x_4147_, 1);
                        v_str_4151_ = leanh::lean_ctor_get(v_pre_4148_, 1);
                        v___x_4152_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_4153_ = lean_string_dec_eq(v_str_4151_, v___x_4152_);
                        if v___x_4153_ == 0 {
                            let mut v___x_4154_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4155_: u8 = 0;
                            v___x_4154_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1;
                            v___x_4155_ = lean_string_dec_eq(v_str_4151_, v___x_4154_);
                            if v___x_4155_ == 0 {
                                return v___y_4145_;
                            } else {
                                let mut v___x_4156_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4157_: u8 = 0;
                                v___x_4156_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2;
                                v___x_4157_ = lean_string_dec_eq(v_str_4150_, v___x_4156_);
                                if v___x_4157_ == 0 {
                                    return v___y_4145_;
                                } else {
                                    return v_suppressElabErrors_4146_;
                                }
                            }
                        } else {
                            let mut v___x_4158_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4159_: u8 = 0;
                            v___x_4158_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3;
                            v___x_4159_ = lean_string_dec_eq(v_str_4150_, v___x_4158_);
                            if v___x_4159_ == 0 {
                                return v___y_4145_;
                            } else {
                                return v_suppressElabErrors_4146_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4160_ = leanh::lean_ctor_get(v_pre_4149_, 0);
                        if leanh::lean_obj_tag(v_pre_4160_) == 0 {
                            let mut v_str_4161_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4162_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4163_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4164_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4165_: u8 = 0;
                            v_str_4161_ = leanh::lean_ctor_get(v_x_4147_, 1);
                            v_str_4162_ = leanh::lean_ctor_get(v_pre_4148_, 1);
                            v_str_4163_ = leanh::lean_ctor_get(v_pre_4149_, 1);
                            v___x_4164_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4;
                            v___x_4165_ = lean_string_dec_eq(v_str_4163_, v___x_4164_);
                            if v___x_4165_ == 0 {
                                return v___y_4145_;
                            } else {
                                let mut v___x_4166_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4167_: u8 = 0;
                                v___x_4166_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5;
                                v___x_4167_ = lean_string_dec_eq(v_str_4162_, v___x_4166_);
                                if v___x_4167_ == 0 {
                                    return v___y_4145_;
                                } else {
                                    let mut v___x_4168_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4169_: u8 = 0;
                                    v___x_4168_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6;
                                    v___x_4169_ = lean_string_dec_eq(v_str_4161_, v___x_4168_);
                                    if v___x_4169_ == 0 {
                                        return v___y_4145_;
                                    } else {
                                        return v_suppressElabErrors_4146_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4145_;
                        }
                    }
                    _ => {
                        return v___y_4145_;
                    }
                }
            }
            0 => {
                let mut v_str_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4172_: u8 = 0;
                v_str_4170_ = leanh::lean_ctor_get(v_x_4147_, 1);
                v___x_4171_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7;
                v___x_4172_ = lean_string_dec_eq(v_str_4170_, v___x_4171_);
                if v___x_4172_ == 0 {
                    return v___y_4145_;
                } else {
                    return v_suppressElabErrors_4146_;
                }
            }
            _ => {
                return v___y_4145_;
            }
        }
    } else {
        return v___y_4145_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed(
    mut v___y_4173_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_4174_: *mut leanh::LeanObject,
    mut v_x_4175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_13717__boxed_4176_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4177_: u8 = 0;
    let mut v_res_4178_: u8 = 0;
    let mut v_r_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_13717__boxed_4176_ = (leanh::lean_unbox(v___y_4173_) as u8);
    v_suppressElabErrors_boxed_4177_ = (leanh::lean_unbox(v_suppressElabErrors_4174_) as u8);
    v_res_4178_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0(v___y_13717__boxed_4176_, v_suppressElabErrors_boxed_4177_, v_x_4175_);
    leanh::lean_dec(v_x_4175_);
    v_r_4179_ = leanh::lean_box((v_res_4178_) as usize);
    return v_r_4179_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1_spec__4(
    mut v_opts_4180_: *mut leanh::LeanObject,
    mut v_opt_4181_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4182_ = leanh::lean_ctor_get(v_opt_4181_, 0);
    v_defValue_4183_ = leanh::lean_ctor_get(v_opt_4181_, 1);
    v_map_4184_ = leanh::lean_ctor_get(v_opts_4180_, 0);
    v___x_4185_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4184_,
            v_name_4182_,
        );
    if leanh::lean_obj_tag(v___x_4185_) == 0 {
        let mut v___x_4186_: u8 = 0;
        v___x_4186_ = (leanh::lean_unbox(v_defValue_4183_) as u8);
        return v___x_4186_;
    } else {
        let mut v_val_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4187_ = leanh::lean_ctor_get(v___x_4185_, 0);
        leanh::lean_inc(v_val_4187_);
        leanh::lean_dec_ref_known(v___x_4185_, 1);
        if leanh::lean_obj_tag(v_val_4187_) == 1 {
            let mut v_v_4188_: u8 = 0;
            v_v_4188_ = leanh::lean_ctor_get_uint8(v_val_4187_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_4187_, 0);
            return v_v_4188_;
        } else {
            let mut v___x_4189_: u8 = 0;
            leanh::lean_dec(v_val_4187_);
            v___x_4189_ = (leanh::lean_unbox(v_defValue_4183_) as u8);
            return v___x_4189_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_opts_4190_: *mut leanh::LeanObject,
    mut v_opt_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4192_: u8 = 0;
    let mut v_r_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4192_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1_spec__4(v_opts_4190_, v_opt_4191_);
    leanh::lean_dec_ref(v_opt_4191_);
    leanh::lean_dec_ref(v_opts_4190_);
    v_r_4193_ = leanh::lean_box((v_res_4192_) as usize);
    return v_r_4193_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1(
    mut v_ref_4194_: *mut leanh::LeanObject,
    mut v_msgData_4195_: *mut leanh::LeanObject,
    mut v_severity_4196_: u8,
    mut v_isSilent_4197_: u8,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4207_: u8 = 0;
    let mut v___y_4208_: u8 = 0;
    let mut v___y_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4227_: u8 = 0;
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v___y_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: u8 = 0;
    let mut v___y_4242_: u8 = 0;
    let mut v___y_4243_: u8 = 0;
    let mut v___y_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut v___y_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: u8 = 0;
    let mut v___y_4267_: u8 = 0;
    let mut v___y_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: u8 = 0;
    let mut v___y_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4278_: u8 = 0;
    let mut v___y_4279_: u8 = 0;
    let mut v___y_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4282_: u8 = 0;
    let mut v_ref_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___y_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4290_: u8 = 0;
    let mut v___y_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4294_: u8 = 0;
    let mut v___y_4295_: u8 = 0;
    let mut v___y_4297_: u8 = 0;
    let mut v_fileName_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4302_: u8 = 0;
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: u8 = 0;
    let mut v___x_4313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4287_ = 2;
                v___x_4312_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4196_, v___x_4287_);
                if v___x_4312_ == 0 {
                    v___y_4297_ = v___x_4312_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_4195_);
                    v___x_4313_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4195_);
                    v___y_4297_ = v___x_4313_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4213_ = lean_st_ref_take(v___y_4212_);
                v_currNamespace_4214_ = leanh::lean_ctor_get(v___y_4211_, 6);
                v_openDecls_4215_ = leanh::lean_ctor_get(v___y_4211_, 7);
                v_env_4216_ = leanh::lean_ctor_get(v___x_4213_, 0);
                v_nextMacroScope_4217_ = leanh::lean_ctor_get(v___x_4213_, 1);
                v_ngen_4218_ = leanh::lean_ctor_get(v___x_4213_, 2);
                v_auxDeclNGen_4219_ = leanh::lean_ctor_get(v___x_4213_, 3);
                v_traceState_4220_ = leanh::lean_ctor_get(v___x_4213_, 4);
                v_cache_4221_ = leanh::lean_ctor_get(v___x_4213_, 5);
                v_messages_4222_ = leanh::lean_ctor_get(v___x_4213_, 6);
                v_infoState_4223_ = leanh::lean_ctor_get(v___x_4213_, 7);
                v_snapshotTasks_4224_ = leanh::lean_ctor_get(v___x_4213_, 8);
                v_isSharedCheck_4238_ = (!leanh::lean_is_exclusive(v___x_4213_)) as u8;
                if v_isSharedCheck_4238_ == 0 {
                    v___x_4226_ = v___x_4213_;
                    v_isShared_4227_ = v_isSharedCheck_4238_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4224_);
                    leanh::lean_inc(v_infoState_4223_);
                    leanh::lean_inc(v_messages_4222_);
                    leanh::lean_inc(v_cache_4221_);
                    leanh::lean_inc(v_traceState_4220_);
                    leanh::lean_inc(v_auxDeclNGen_4219_);
                    leanh::lean_inc(v_ngen_4218_);
                    leanh::lean_inc(v_nextMacroScope_4217_);
                    leanh::lean_inc(v_env_4216_);
                    leanh::lean_dec(v___x_4213_);
                    v___x_4226_ = leanh::lean_box(0);
                    v_isShared_4227_ = v_isSharedCheck_4238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_4215_);
                leanh::lean_inc(v_currNamespace_4214_);
                v___x_4228_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4228_, 0, v_currNamespace_4214_);
                leanh::lean_ctor_set(v___x_4228_, 1, v_openDecls_4215_);
                v___x_4229_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4229_, 0, v___x_4228_);
                leanh::lean_ctor_set(v___x_4229_, 1, v___y_4204_);
                leanh::lean_inc_ref(v___y_4206_);
                leanh::lean_inc_ref(v___y_4210_);
                v___x_4230_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_4230_, 0, v___y_4210_);
                leanh::lean_ctor_set(v___x_4230_, 1, v___y_4205_);
                leanh::lean_ctor_set(v___x_4230_, 2, v___y_4209_);
                leanh::lean_ctor_set(v___x_4230_, 3, v___y_4206_);
                leanh::lean_ctor_set(v___x_4230_, 4, v___x_4229_);
                leanh::lean_ctor_set_uint8(
                    v___x_4230_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_4207_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4230_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4208_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4230_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4197_,
                );
                v___x_4231_ = l_Lean_MessageLog_add(v___x_4230_, v_messages_4222_);
                if v_isShared_4227_ == 0 {
                    leanh::lean_ctor_set(v___x_4226_, 6, v___x_4231_);
                    v___x_4233_ = v___x_4226_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_env_4216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_nextMacroScope_4217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 2, v_ngen_4218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 3, v_auxDeclNGen_4219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 4, v_traceState_4220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 5, v_cache_4221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 6, v___x_4231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 7, v_infoState_4223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 8, v_snapshotTasks_4224_);
                    v___x_4233_ = v_reuseFailAlloc_4237_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4234_ = lean_st_ref_set(v___y_4212_, v___x_4233_);
                v___x_4235_ = leanh::lean_box(0);
                v___x_4236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4236_, 0, v___x_4235_);
                return v___x_4236_;
            }
            4 => {
                v___x_4248_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4195_,
                    );
                v___x_4249_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(v___x_4248_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
                v_a_4250_ = leanh::lean_ctor_get(v___x_4249_, 0);
                v_isSharedCheck_4263_ = (!leanh::lean_is_exclusive(v___x_4249_)) as u8;
                if v_isSharedCheck_4263_ == 0 {
                    v___x_4252_ = v___x_4249_;
                    v_isShared_4253_ = v_isSharedCheck_4263_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4250_);
                    leanh::lean_dec(v___x_4249_);
                    v___x_4252_ = leanh::lean_box(0);
                    v_isShared_4253_ = v_isSharedCheck_4263_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_4246_, 2);
                v___x_4254_ = l_Lean_FileMap_toPosition(v___y_4246_, v___y_4244_);
                leanh::lean_dec(v___y_4244_);
                v___x_4255_ = l_Lean_FileMap_toPosition(v___y_4246_, v___y_4247_);
                leanh::lean_dec(v___y_4247_);
                v___x_4256_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4256_, 0, v___x_4255_);
                v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
                if v___y_4241_ == 0 {
                    leanh::lean_del_object(v___x_4252_);
                    leanh::lean_dec_ref(v___y_4240_);
                    v___y_4204_ = v_a_4250_;
                    v___y_4205_ = v___x_4254_;
                    v___y_4206_ = v___x_4257_;
                    v___y_4207_ = v___y_4242_;
                    v___y_4208_ = v___y_4243_;
                    v___y_4209_ = v___x_4256_;
                    v___y_4210_ = v___y_4245_;
                    v___y_4211_ = v___y_4200_;
                    v___y_4212_ = v___y_4201_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4250_);
                    v___x_4258_ = l_Lean_MessageData_hasTag(v___y_4240_, v_a_4250_);
                    if v___x_4258_ == 0 {
                        leanh::lean_dec_ref_known(v___x_4256_, 1);
                        leanh::lean_dec_ref(v___x_4254_);
                        leanh::lean_dec(v_a_4250_);
                        v___x_4259_ = leanh::lean_box(0);
                        if v_isShared_4253_ == 0 {
                            leanh::lean_ctor_set(v___x_4252_, 0, v___x_4259_);
                            v___x_4261_ = v___x_4252_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4262_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
                            v___x_4261_ = v_reuseFailAlloc_4262_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4252_);
                        v___y_4204_ = v_a_4250_;
                        v___y_4205_ = v___x_4254_;
                        v___y_4206_ = v___x_4257_;
                        v___y_4207_ = v___y_4242_;
                        v___y_4208_ = v___y_4243_;
                        v___y_4209_ = v___x_4256_;
                        v___y_4210_ = v___y_4245_;
                        v___y_4211_ = v___y_4200_;
                        v___y_4212_ = v___y_4201_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4261_;
            }
            7 => {
                v___x_4273_ = l_Lean_Syntax_getTailPos_x3f(v___y_4268_, v___y_4267_);
                leanh::lean_dec(v___y_4268_);
                if leanh::lean_obj_tag(v___x_4273_) == 0 {
                    leanh::lean_inc(v___y_4272_);
                    v___y_4240_ = v___y_4265_;
                    v___y_4241_ = v___y_4266_;
                    v___y_4242_ = v___y_4267_;
                    v___y_4243_ = v___y_4269_;
                    v___y_4244_ = v___y_4272_;
                    v___y_4245_ = v___y_4271_;
                    v___y_4246_ = v___y_4270_;
                    v___y_4247_ = v___y_4272_;
                    state = 4;
                    continue;
                } else {
                    v_val_4274_ = leanh::lean_ctor_get(v___x_4273_, 0);
                    leanh::lean_inc(v_val_4274_);
                    leanh::lean_dec_ref_known(v___x_4273_, 1);
                    v___y_4240_ = v___y_4265_;
                    v___y_4241_ = v___y_4266_;
                    v___y_4242_ = v___y_4267_;
                    v___y_4243_ = v___y_4269_;
                    v___y_4244_ = v___y_4272_;
                    v___y_4245_ = v___y_4271_;
                    v___y_4246_ = v___y_4270_;
                    v___y_4247_ = v_val_4274_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4283_ = l_Lean_replaceRef(v_ref_4194_, v___y_4277_);
                v___x_4284_ = l_Lean_Syntax_getPos_x3f(v_ref_4283_, v___y_4279_);
                if leanh::lean_obj_tag(v___x_4284_) == 0 {
                    v___x_4285_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4265_ = v___y_4276_;
                    v___y_4266_ = v___y_4278_;
                    v___y_4267_ = v___y_4279_;
                    v___y_4268_ = v_ref_4283_;
                    v___y_4269_ = v___y_4282_;
                    v___y_4270_ = v___y_4281_;
                    v___y_4271_ = v___y_4280_;
                    v___y_4272_ = v___x_4285_;
                    state = 7;
                    continue;
                } else {
                    v_val_4286_ = leanh::lean_ctor_get(v___x_4284_, 0);
                    leanh::lean_inc(v_val_4286_);
                    leanh::lean_dec_ref_known(v___x_4284_, 1);
                    v___y_4265_ = v___y_4276_;
                    v___y_4266_ = v___y_4278_;
                    v___y_4267_ = v___y_4279_;
                    v___y_4268_ = v_ref_4283_;
                    v___y_4269_ = v___y_4282_;
                    v___y_4270_ = v___y_4281_;
                    v___y_4271_ = v___y_4280_;
                    v___y_4272_ = v_val_4286_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4295_ == 0 {
                    v___y_4276_ = v___y_4291_;
                    v___y_4277_ = v___y_4289_;
                    v___y_4278_ = v___y_4290_;
                    v___y_4279_ = v___y_4294_;
                    v___y_4280_ = v___y_4293_;
                    v___y_4281_ = v___y_4292_;
                    v___y_4282_ = v_severity_4196_;
                    state = 8;
                    continue;
                } else {
                    v___y_4276_ = v___y_4291_;
                    v___y_4277_ = v___y_4289_;
                    v___y_4278_ = v___y_4290_;
                    v___y_4279_ = v___y_4294_;
                    v___y_4280_ = v___y_4293_;
                    v___y_4281_ = v___y_4292_;
                    v___y_4282_ = v___x_4287_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4297_ == 0 {
                    v_fileName_4298_ = leanh::lean_ctor_get(v___y_4200_, 0);
                    v_fileMap_4299_ = leanh::lean_ctor_get(v___y_4200_, 1);
                    v_options_4300_ = leanh::lean_ctor_get(v___y_4200_, 2);
                    v_ref_4301_ = leanh::lean_ctor_get(v___y_4200_, 5);
                    v_suppressElabErrors_4302_ = leanh::lean_ctor_get_uint8(
                        v___y_4200_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4303_ = leanh::lean_box((v___y_4297_) as usize);
                    v___x_4304_ = leanh::lean_box((v_suppressElabErrors_4302_) as usize);
                    v___f_4305_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_4305_, 0, v___x_4303_);
                    leanh::lean_closure_set(v___f_4305_, 1, v___x_4304_);
                    v___x_4306_ = 1;
                    v___x_4307_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4196_, v___x_4306_);
                    if v___x_4307_ == 0 {
                        v___y_4289_ = v_ref_4301_;
                        v___y_4290_ = v_suppressElabErrors_4302_;
                        v___y_4291_ = v___f_4305_;
                        v___y_4292_ = v_fileMap_4299_;
                        v___y_4293_ = v_fileName_4298_;
                        v___y_4294_ = v___y_4297_;
                        v___y_4295_ = v___x_4307_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4308_ = l_Lean_warningAsError;
                        v___x_4309_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1_spec__4(v_options_4300_, v___x_4308_);
                        v___y_4289_ = v_ref_4301_;
                        v___y_4290_ = v_suppressElabErrors_4302_;
                        v___y_4291_ = v___f_4305_;
                        v___y_4292_ = v_fileMap_4299_;
                        v___y_4293_ = v_fileName_4298_;
                        v___y_4294_ = v___y_4297_;
                        v___y_4295_ = v___x_4309_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_4195_);
                    v___x_4310_ = leanh::lean_box(0);
                    v___x_4311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4311_, 0, v___x_4310_);
                    return v___x_4311_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___boxed(
    mut v_ref_4314_: *mut leanh::LeanObject,
    mut v_msgData_4315_: *mut leanh::LeanObject,
    mut v_severity_4316_: *mut leanh::LeanObject,
    mut v_isSilent_4317_: *mut leanh::LeanObject,
    mut v___y_4318_: *mut leanh::LeanObject,
    mut v___y_4319_: *mut leanh::LeanObject,
    mut v___y_4320_: *mut leanh::LeanObject,
    mut v___y_4321_: *mut leanh::LeanObject,
    mut v___y_4322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_4323_: u8 = 0;
    let mut v_isSilent_boxed_4324_: u8 = 0;
    let mut v_res_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4323_ = (leanh::lean_unbox(v_severity_4316_) as u8);
    v_isSilent_boxed_4324_ = (leanh::lean_unbox(v_isSilent_4317_) as u8);
    v_res_4325_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1(v_ref_4314_, v_msgData_4315_, v_severity_boxed_4323_, v_isSilent_boxed_4324_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
    leanh::lean_dec(v___y_4321_);
    leanh::lean_dec_ref(v___y_4320_);
    leanh::lean_dec(v___y_4319_);
    leanh::lean_dec_ref(v___y_4318_);
    leanh::lean_dec(v_ref_4314_);
    return v_res_4325_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0(
    mut v_msgData_4326_: *mut leanh::LeanObject,
    mut v_severity_4327_: u8,
    mut v_isSilent_4328_: u8,
    mut v___y_4329_: *mut leanh::LeanObject,
    mut v___y_4330_: *mut leanh::LeanObject,
    mut v___y_4331_: *mut leanh::LeanObject,
    mut v___y_4332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4334_ = leanh::lean_ctor_get(v___y_4331_, 5);
    v___x_4335_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1(v_ref_4334_, v_msgData_4326_, v_severity_4327_, v_isSilent_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
    return v___x_4335_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0___boxed(
    mut v_msgData_4336_: *mut leanh::LeanObject,
    mut v_severity_4337_: *mut leanh::LeanObject,
    mut v_isSilent_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_4344_: u8 = 0;
    let mut v_isSilent_boxed_4345_: u8 = 0;
    let mut v_res_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4344_ = (leanh::lean_unbox(v_severity_4337_) as u8);
    v_isSilent_boxed_4345_ = (leanh::lean_unbox(v_isSilent_4338_) as u8);
    v_res_4346_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0(
        v_msgData_4336_,
        v_severity_boxed_4344_,
        v_isSilent_boxed_4345_,
        v___y_4339_,
        v___y_4340_,
        v___y_4341_,
        v___y_4342_,
    );
    leanh::lean_dec(v___y_4342_);
    leanh::lean_dec_ref(v___y_4341_);
    leanh::lean_dec(v___y_4340_);
    leanh::lean_dec_ref(v___y_4339_);
    return v_res_4346_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0(
    mut v_msgData_4347_: *mut leanh::LeanObject,
    mut v___y_4348_: *mut leanh::LeanObject,
    mut v___y_4349_: *mut leanh::LeanObject,
    mut v___y_4350_: *mut leanh::LeanObject,
    mut v___y_4351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = 0;
    v___x_4354_ = 0;
    v___x_4355_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0(
        v_msgData_4347_,
        v___x_4353_,
        v___x_4354_,
        v___y_4348_,
        v___y_4349_,
        v___y_4350_,
        v___y_4351_,
    );
    return v___x_4355_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0___boxed(
    mut v_msgData_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4362_ = l_Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0(
        v_msgData_4356_,
        v___y_4357_,
        v___y_4358_,
        v___y_4359_,
        v___y_4360_,
    );
    leanh::lean_dec(v___y_4360_);
    leanh::lean_dec_ref(v___y_4359_);
    leanh::lean_dec(v___y_4358_);
    leanh::lean_dec_ref(v___y_4357_);
    return v_res_4362_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4363_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4363_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__0_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__0,
    );
    v___x_4365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4365_, 0, v___x_4364_);
    return v___x_4365_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4367_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4367_, 0, v___x_4366_);
    leanh::lean_ctor_set(v___x_4367_, 1, v___x_4366_);
    leanh::lean_ctor_set(v___x_4367_, 2, v___x_4366_);
    leanh::lean_ctor_set(v___x_4367_, 3, v___x_4366_);
    leanh::lean_ctor_set(v___x_4367_, 4, v___x_4366_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4368_ = 0;
    v___x_4369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4370_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_4370_, 0, v___x_4369_);
    leanh::lean_ctor_set_uint8(
        v___x_4370_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_4368_,
    );
    return v___x_4370_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4371_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4372_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4372_, 0, v___x_4371_);
    leanh::lean_ctor_set(v___x_4372_, 1, v___x_4371_);
    return v___x_4372_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4374_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_4374_, 0, v___x_4373_);
    leanh::lean_ctor_set(v___x_4374_, 1, v___x_4373_);
    leanh::lean_ctor_set(v___x_4374_, 2, v___x_4373_);
    leanh::lean_ctor_set(v___x_4374_, 3, v___x_4373_);
    leanh::lean_ctor_set(v___x_4374_, 4, v___x_4373_);
    leanh::lean_ctor_set(v___x_4374_, 5, v___x_4373_);
    return v___x_4374_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__20() -> *mut leanh::LeanObject
{
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4392_ = l_Lean_Meta_reportDiag___lam__1___closed__19;
    v___x_4393_ = l_Lean_MessageData_ofFormat(v___x_4392_);
    return v___x_4393_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__23() -> *mut leanh::LeanObject
{
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: u8 = 0;
    let mut v___x_4399_: f64 = 0.0;
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
    v___x_4398_ = 0;
    v___x_4399_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0);
    v___x_4400_ = leanh::lean_box(0);
    v___x_4401_ = l_Lean_Meta_reportDiag___lam__1___closed__22;
    v___x_4402_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_4402_, 0, v___x_4401_);
    leanh::lean_ctor_set(v___x_4402_, 1, v___x_4400_);
    leanh::lean_ctor_set(v___x_4402_, 2, v___x_4397_);
    leanh::lean_ctor_set_float(
        v___x_4402_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_4399_,
    );
    leanh::lean_ctor_set_float(
        v___x_4402_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_4399_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4402_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_4398_,
    );
    return v___x_4402_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__26() -> *mut leanh::LeanObject
{
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4406_ = l_Lean_Meta_reportDiag___lam__1___closed__25;
    v___x_4407_ = l_Lean_MessageData_ofFormat(v___x_4406_);
    return v___x_4407_;
}
pub unsafe fn l_Lean_Meta_reportDiag___lam__1(
    mut v_a_4408_: u8,
    mut v___f_4409_: *mut leanh::LeanObject,
    mut v___y_4410_: *mut leanh::LeanObject,
    mut v___y_4411_: *mut leanh::LeanObject,
    mut v___y_4412_: *mut leanh::LeanObject,
    mut v___y_4413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: u8 = 0;
    let mut v___y_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4429_: u8 = 0;
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4445_: u8 = 0;
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4459_: u8 = 0;
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_unused_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_unused_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut v_unused_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldAxiomCounter_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_heuristicCounter_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingFailures_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v_a_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut v_a_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_a_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4567_: u8 = 0;
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_a_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4575_: u8 = 0;
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut v_a_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut v_a_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut v_a_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4415_ = lean_st_ref_get(v___y_4411_);
                v_diag_4416_ = leanh::lean_ctor_get(v___x_4415_, 4);
                leanh::lean_inc_ref(v_diag_4416_);
                leanh::lean_dec(v___x_4415_);
                v_unfoldCounter_4417_ = leanh::lean_ctor_get(v_diag_4416_, 0);
                leanh::lean_inc_ref(v_unfoldCounter_4417_);
                leanh::lean_dec_ref(v_diag_4416_);
                v___x_4418_ = 0;
                v___x_4475_ = l_Lean_Meta_mkDiagSummaryForUnfolded(
                    v_unfoldCounter_4417_,
                    v___x_4418_,
                    v___y_4410_,
                    v___y_4411_,
                    v___y_4412_,
                    v___y_4413_,
                );
                if leanh::lean_obj_tag(v___x_4475_) == 0 {
                    v_a_4476_ = leanh::lean_ctor_get(v___x_4475_, 0);
                    leanh::lean_inc(v_a_4476_);
                    leanh::lean_dec_ref_known(v___x_4475_, 1);
                    v___x_4477_ = l_Lean_Meta_mkDiagSummaryForUnfolded(
                        v_unfoldCounter_4417_,
                        v_a_4408_,
                        v___y_4410_,
                        v___y_4411_,
                        v___y_4412_,
                        v___y_4413_,
                    );
                    if leanh::lean_obj_tag(v___x_4477_) == 0 {
                        v_a_4478_ = leanh::lean_ctor_get(v___x_4477_, 0);
                        leanh::lean_inc(v_a_4478_);
                        leanh::lean_dec_ref_known(v___x_4477_, 1);
                        v___x_4479_ = lean_st_ref_get(v___y_4411_);
                        v_diag_4480_ = leanh::lean_ctor_get(v___x_4479_, 4);
                        leanh::lean_inc_ref(v_diag_4480_);
                        leanh::lean_dec(v___x_4479_);
                        v_unfoldAxiomCounter_4481_ = leanh::lean_ctor_get(v_diag_4480_, 1);
                        leanh::lean_inc_ref(v_unfoldAxiomCounter_4481_);
                        leanh::lean_dec_ref(v_diag_4480_);
                        v___x_4482_ = l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1;
                        leanh::lean_inc_ref(v___f_4409_);
                        v___x_4483_ = l_Lean_Meta_mkDiagSummary(
                            v___x_4482_,
                            v_unfoldAxiomCounter_4481_,
                            v___f_4409_,
                            v___y_4410_,
                            v___y_4411_,
                            v___y_4412_,
                            v___y_4413_,
                        );
                        leanh::lean_dec_ref(v_unfoldAxiomCounter_4481_);
                        if leanh::lean_obj_tag(v___x_4483_) == 0 {
                            v_a_4484_ = leanh::lean_ctor_get(v___x_4483_, 0);
                            leanh::lean_inc(v_a_4484_);
                            leanh::lean_dec_ref_known(v___x_4483_, 1);
                            v___x_4485_ = l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(
                                v_unfoldCounter_4417_,
                                v___y_4410_,
                                v___y_4411_,
                                v___y_4412_,
                                v___y_4413_,
                            );
                            leanh::lean_dec_ref(v_unfoldCounter_4417_);
                            if leanh::lean_obj_tag(v___x_4485_) == 0 {
                                v_a_4486_ = leanh::lean_ctor_get(v___x_4485_, 0);
                                leanh::lean_inc(v_a_4486_);
                                leanh::lean_dec_ref_known(v___x_4485_, 1);
                                v___x_4487_ = lean_st_ref_get(v___y_4411_);
                                v_diag_4488_ = leanh::lean_ctor_get(v___x_4487_, 4);
                                leanh::lean_inc_ref(v_diag_4488_);
                                leanh::lean_dec(v___x_4487_);
                                v_heuristicCounter_4489_ =
                                    leanh::lean_ctor_get(v_diag_4488_, 2);
                                leanh::lean_inc_ref(v_heuristicCounter_4489_);
                                leanh::lean_dec_ref(v_diag_4488_);
                                v___x_4490_ = l_Lean_Meta_reportDiag___lam__1___closed__7;
                                leanh::lean_inc_ref(v___f_4409_);
                                v___x_4491_ = l_Lean_Meta_mkDiagSummary(
                                    v___x_4490_,
                                    v_heuristicCounter_4489_,
                                    v___f_4409_,
                                    v___y_4410_,
                                    v___y_4411_,
                                    v___y_4412_,
                                    v___y_4413_,
                                );
                                leanh::lean_dec_ref(v_heuristicCounter_4489_);
                                if leanh::lean_obj_tag(v___x_4491_) == 0 {
                                    v_a_4492_ = leanh::lean_ctor_get(v___x_4491_, 0);
                                    leanh::lean_inc(v_a_4492_);
                                    leanh::lean_dec_ref_known(v___x_4491_, 1);
                                    v___x_4493_ = l_Lean_Meta_mkDiagSummaryForUsedInstances(
                                        v___y_4410_,
                                        v___y_4411_,
                                        v___y_4412_,
                                        v___y_4413_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4493_) == 0 {
                                        v_a_4494_ = leanh::lean_ctor_get(v___x_4493_, 0);
                                        leanh::lean_inc(v_a_4494_);
                                        leanh::lean_dec_ref_known(v___x_4493_, 1);
                                        v___x_4495_ = lean_st_ref_get(v___y_4411_);
                                        v_diag_4496_ = leanh::lean_ctor_get(v___x_4495_, 4);
                                        leanh::lean_inc_ref(v_diag_4496_);
                                        leanh::lean_dec(v___x_4495_);
                                        v_synthPendingFailures_4497_ =
                                            leanh::lean_ctor_get(v_diag_4496_, 4);
                                        leanh::lean_inc_ref(v_synthPendingFailures_4497_);
                                        leanh::lean_dec_ref(v_diag_4496_);
                                        v___x_4498_ = l_Lean_Meta_mkDiagSynthPendingFailure(
                                            v_synthPendingFailures_4497_,
                                            v___y_4410_,
                                            v___y_4411_,
                                            v___y_4412_,
                                            v___y_4413_,
                                        );
                                        leanh::lean_dec_ref(v_synthPendingFailures_4497_);
                                        if leanh::lean_obj_tag(v___x_4498_) == 0 {
                                            v_a_4499_ = leanh::lean_ctor_get(v___x_4498_, 0);
                                            leanh::lean_inc(v_a_4499_);
                                            leanh::lean_dec_ref_known(v___x_4498_, 1);
                                            v___x_4500_ = lean_st_ref_get(v___y_4413_);
                                            v_env_4501_ =
                                                leanh::lean_ctor_get(v___x_4500_, 0);
                                            leanh::lean_inc_ref(v_env_4501_);
                                            leanh::lean_dec(v___x_4500_);
                                            v___x_4502_ = l_Lean_Kernel_getDiagnostics(v_env_4501_);
                                            v_unfoldCounter_4503_ =
                                                leanh::lean_ctor_get(v___x_4502_, 0);
                                            leanh::lean_inc_ref(v_unfoldCounter_4503_);
                                            leanh::lean_dec_ref(v___x_4502_);
                                            v___x_4504_ =
                                                l_Lean_Meta_reportDiag___lam__1___closed__9;
                                            v___x_4505_ = l_Lean_Meta_mkDiagSummary(
                                                v___x_4504_,
                                                v_unfoldCounter_4503_,
                                                v___f_4409_,
                                                v___y_4410_,
                                                v___y_4411_,
                                                v___y_4412_,
                                                v___y_4413_,
                                            );
                                            leanh::lean_dec_ref(v_unfoldCounter_4503_);
                                            if leanh::lean_obj_tag(v___x_4505_) == 0 {
                                                v_a_4506_ =
                                                    leanh::lean_ctor_get(v___x_4505_, 0);
                                                leanh::lean_inc(v_a_4506_);
                                                leanh::lean_dec_ref_known(v___x_4505_, 1);
                                                v___x_4507_ = leanh::lean_unsigned_to_nat(0);
                                                v___x_4508_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__0;
                                                v___x_4509_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__10;
                                                v___x_4510_ = l_Lean_Meta_appendSection(
                                                    v___x_4508_,
                                                    v___x_4482_,
                                                    v___x_4509_,
                                                    v_a_4476_,
                                                    v_a_4408_,
                                                );
                                                v_options_4511_ =
                                                    leanh::lean_ctor_get(v___y_4412_, 2);
                                                v___x_4512_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__11;
                                                v___x_4513_ = l_Lean_Meta_appendSection(
                                                    v___x_4510_,
                                                    v___x_4482_,
                                                    v___x_4512_,
                                                    v_a_4478_,
                                                    v_a_4408_,
                                                );
                                                v___x_4514_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__12;
                                                v___x_4515_ = l_Lean_Meta_appendSection(
                                                    v___x_4513_,
                                                    v___x_4482_,
                                                    v___x_4514_,
                                                    v_a_4486_,
                                                    v_a_4408_,
                                                );
                                                v___x_4516_ = l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2;
                                                v___x_4517_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__13;
                                                v___x_4518_ = l_Lean_Meta_appendSection(
                                                    v___x_4515_,
                                                    v___x_4516_,
                                                    v___x_4517_,
                                                    v_a_4494_,
                                                    v_a_4408_,
                                                );
                                                v___x_4519_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__14;
                                                v___x_4520_ = l_Lean_Meta_maxSynthPendingDepth;
                                                v___x_4521_ = l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0(v_options_4511_, v___x_4520_);
                                                v___x_4522_ = l_Nat_reprFast(v___x_4521_);
                                                v___x_4523_ =
                                                    lean_string_append(v___x_4519_, v___x_4522_);
                                                leanh::lean_dec_ref(v___x_4522_);
                                                v___x_4524_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__15;
                                                v___x_4525_ =
                                                    lean_string_append(v___x_4523_, v___x_4524_);
                                                v___x_4526_ = l_Lean_Meta_appendSection(
                                                    v___x_4518_,
                                                    v___x_4516_,
                                                    v___x_4525_,
                                                    v_a_4499_,
                                                    v___x_4418_,
                                                );
                                                v___x_4527_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__16;
                                                v___x_4528_ = l_Lean_Meta_appendSection(
                                                    v___x_4526_,
                                                    v___x_4490_,
                                                    v___x_4527_,
                                                    v_a_4492_,
                                                    v_a_4408_,
                                                );
                                                v___x_4529_ =
                                                    l_Lean_Meta_reportDiag___lam__1___closed__17;
                                                v___x_4530_ = l_Lean_Meta_appendSection(
                                                    v___x_4528_,
                                                    v___x_4482_,
                                                    v___x_4529_,
                                                    v_a_4484_,
                                                    v_a_4408_,
                                                );
                                                v___x_4531_ = l_Lean_Meta_appendSection(
                                                    v___x_4530_,
                                                    v___x_4504_,
                                                    v___x_4509_,
                                                    v_a_4506_,
                                                    v_a_4408_,
                                                );
                                                v___x_4532_ = lean_array_get_size(v___x_4531_);
                                                v___x_4533_ =
                                                    lean_nat_dec_eq(v___x_4532_, v___x_4507_);
                                                if v___x_4533_ == 0 {
                                                    v___x_4534_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__20), core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__20_once), _init_l_Lean_Meta_reportDiag___lam__1___closed__20);
                                                    v___x_4535_ =
                                                        lean_array_push(v___x_4531_, v___x_4534_);
                                                    v___x_4536_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__23), core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__23_once), _init_l_Lean_Meta_reportDiag___lam__1___closed__23);
                                                    v___x_4537_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__26), core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__26_once), _init_l_Lean_Meta_reportDiag___lam__1___closed__26);
                                                    v___x_4538_ = leanh::lean_alloc_ctor(
                                                        9,
                                                        3,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4538_,
                                                        0,
                                                        v___x_4536_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4538_,
                                                        1,
                                                        v___x_4537_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4538_,
                                                        2,
                                                        v___x_4535_,
                                                    );
                                                    v___x_4539_ = l_Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0(v___x_4538_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
                                                    if leanh::lean_obj_tag(v___x_4539_) == 0
                                                    {
                                                        leanh::lean_dec_ref_known(
                                                            v___x_4539_,
                                                            1,
                                                        );
                                                        v___y_4420_ = v___y_4411_;
                                                        v___y_4421_ = v___y_4413_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        return v___x_4539_;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_4531_);
                                                    v___y_4420_ = v___y_4411_;
                                                    v___y_4421_ = v___y_4413_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_4499_);
                                                leanh::lean_dec(v_a_4494_);
                                                leanh::lean_dec(v_a_4492_);
                                                leanh::lean_dec(v_a_4486_);
                                                leanh::lean_dec(v_a_4484_);
                                                leanh::lean_dec(v_a_4478_);
                                                leanh::lean_dec(v_a_4476_);
                                                v_a_4540_ =
                                                    leanh::lean_ctor_get(v___x_4505_, 0);
                                                v_isSharedCheck_4547_ =
                                                    (!leanh::lean_is_exclusive(v___x_4505_))
                                                        as u8;
                                                if v_isSharedCheck_4547_ == 0 {
                                                    v___x_4542_ = v___x_4505_;
                                                    v_isShared_4543_ = v_isSharedCheck_4547_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4540_);
                                                    leanh::lean_dec(v___x_4505_);
                                                    v___x_4542_ = leanh::lean_box(0);
                                                    v_isShared_4543_ = v_isSharedCheck_4547_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_4494_);
                                            leanh::lean_dec(v_a_4492_);
                                            leanh::lean_dec(v_a_4486_);
                                            leanh::lean_dec(v_a_4484_);
                                            leanh::lean_dec(v_a_4478_);
                                            leanh::lean_dec(v_a_4476_);
                                            leanh::lean_dec_ref(v___f_4409_);
                                            v_a_4548_ = leanh::lean_ctor_get(v___x_4498_, 0);
                                            v_isSharedCheck_4555_ =
                                                (!leanh::lean_is_exclusive(v___x_4498_))
                                                    as u8;
                                            if v_isSharedCheck_4555_ == 0 {
                                                v___x_4550_ = v___x_4498_;
                                                v_isShared_4551_ = v_isSharedCheck_4555_;
                                                state = 10;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4548_);
                                                leanh::lean_dec(v___x_4498_);
                                                v___x_4550_ = leanh::lean_box(0);
                                                v_isShared_4551_ = v_isSharedCheck_4555_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_4492_);
                                        leanh::lean_dec(v_a_4486_);
                                        leanh::lean_dec(v_a_4484_);
                                        leanh::lean_dec(v_a_4478_);
                                        leanh::lean_dec(v_a_4476_);
                                        leanh::lean_dec_ref(v___f_4409_);
                                        v_a_4556_ = leanh::lean_ctor_get(v___x_4493_, 0);
                                        v_isSharedCheck_4563_ =
                                            (!leanh::lean_is_exclusive(v___x_4493_)) as u8;
                                        if v_isSharedCheck_4563_ == 0 {
                                            v___x_4558_ = v___x_4493_;
                                            v_isShared_4559_ = v_isSharedCheck_4563_;
                                            state = 12;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4556_);
                                            leanh::lean_dec(v___x_4493_);
                                            v___x_4558_ = leanh::lean_box(0);
                                            v_isShared_4559_ = v_isSharedCheck_4563_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4486_);
                                    leanh::lean_dec(v_a_4484_);
                                    leanh::lean_dec(v_a_4478_);
                                    leanh::lean_dec(v_a_4476_);
                                    leanh::lean_dec_ref(v___f_4409_);
                                    v_a_4564_ = leanh::lean_ctor_get(v___x_4491_, 0);
                                    v_isSharedCheck_4571_ =
                                        (!leanh::lean_is_exclusive(v___x_4491_)) as u8;
                                    if v_isSharedCheck_4571_ == 0 {
                                        v___x_4566_ = v___x_4491_;
                                        v_isShared_4567_ = v_isSharedCheck_4571_;
                                        state = 14;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4564_);
                                        leanh::lean_dec(v___x_4491_);
                                        v___x_4566_ = leanh::lean_box(0);
                                        v_isShared_4567_ = v_isSharedCheck_4571_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_4484_);
                                leanh::lean_dec(v_a_4478_);
                                leanh::lean_dec(v_a_4476_);
                                leanh::lean_dec_ref(v___f_4409_);
                                v_a_4572_ = leanh::lean_ctor_get(v___x_4485_, 0);
                                v_isSharedCheck_4579_ =
                                    (!leanh::lean_is_exclusive(v___x_4485_)) as u8;
                                if v_isSharedCheck_4579_ == 0 {
                                    v___x_4574_ = v___x_4485_;
                                    v_isShared_4575_ = v_isSharedCheck_4579_;
                                    state = 16;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4572_);
                                    leanh::lean_dec(v___x_4485_);
                                    v___x_4574_ = leanh::lean_box(0);
                                    v_isShared_4575_ = v_isSharedCheck_4579_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4478_);
                            leanh::lean_dec(v_a_4476_);
                            leanh::lean_dec_ref(v_unfoldCounter_4417_);
                            leanh::lean_dec_ref(v___f_4409_);
                            v_a_4580_ = leanh::lean_ctor_get(v___x_4483_, 0);
                            v_isSharedCheck_4587_ =
                                (!leanh::lean_is_exclusive(v___x_4483_)) as u8;
                            if v_isSharedCheck_4587_ == 0 {
                                v___x_4582_ = v___x_4483_;
                                v_isShared_4583_ = v_isSharedCheck_4587_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4580_);
                                leanh::lean_dec(v___x_4483_);
                                v___x_4582_ = leanh::lean_box(0);
                                v_isShared_4583_ = v_isSharedCheck_4587_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4476_);
                        leanh::lean_dec_ref(v_unfoldCounter_4417_);
                        leanh::lean_dec_ref(v___f_4409_);
                        v_a_4588_ = leanh::lean_ctor_get(v___x_4477_, 0);
                        v_isSharedCheck_4595_ =
                            (!leanh::lean_is_exclusive(v___x_4477_)) as u8;
                        if v_isSharedCheck_4595_ == 0 {
                            v___x_4590_ = v___x_4477_;
                            v_isShared_4591_ = v_isSharedCheck_4595_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4588_);
                            leanh::lean_dec(v___x_4477_);
                            v___x_4590_ = leanh::lean_box(0);
                            v_isShared_4591_ = v_isSharedCheck_4595_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_unfoldCounter_4417_);
                    leanh::lean_dec_ref(v___f_4409_);
                    v_a_4596_ = leanh::lean_ctor_get(v___x_4475_, 0);
                    v_isSharedCheck_4603_ = (!leanh::lean_is_exclusive(v___x_4475_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4598_ = v___x_4475_;
                        v_isShared_4599_ = v_isSharedCheck_4603_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4596_);
                        leanh::lean_dec(v___x_4475_);
                        v___x_4598_ = leanh::lean_box(0);
                        v_isShared_4599_ = v_isSharedCheck_4603_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4422_ = lean_st_ref_take(v___y_4420_);
                v_mctx_4423_ = leanh::lean_ctor_get(v___x_4422_, 0);
                v_cache_4424_ = leanh::lean_ctor_get(v___x_4422_, 1);
                v_zetaDeltaFVarIds_4425_ = leanh::lean_ctor_get(v___x_4422_, 2);
                v_postponed_4426_ = leanh::lean_ctor_get(v___x_4422_, 3);
                v_isSharedCheck_4473_ = (!leanh::lean_is_exclusive(v___x_4422_)) as u8;
                if v_isSharedCheck_4473_ == 0 {
                    v_unused_4474_ = leanh::lean_ctor_get(v___x_4422_, 4);
                    leanh::lean_dec(v_unused_4474_);
                    v___x_4428_ = v___x_4422_;
                    v_isShared_4429_ = v_isSharedCheck_4473_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_postponed_4426_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4425_);
                    leanh::lean_inc(v_cache_4424_);
                    leanh::lean_inc(v_mctx_4423_);
                    leanh::lean_dec(v___x_4422_);
                    v___x_4428_ = leanh::lean_box(0);
                    v_isShared_4429_ = v_isSharedCheck_4473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4430_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__2_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__2,
                );
                if v_isShared_4429_ == 0 {
                    leanh::lean_ctor_set(v___x_4428_, 4, v___x_4430_);
                    v___x_4432_ = v___x_4428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_mctx_4423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_cache_4424_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4472_,
                        2,
                        v_zetaDeltaFVarIds_4425_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 3, v_postponed_4426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 4, v___x_4430_);
                    v___x_4432_ = v_reuseFailAlloc_4472_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4433_ = lean_st_ref_set(v___y_4420_, v___x_4432_);
                v___x_4434_ = lean_st_ref_take(v___y_4421_);
                v_env_4435_ = leanh::lean_ctor_get(v___x_4434_, 0);
                v_nextMacroScope_4436_ = leanh::lean_ctor_get(v___x_4434_, 1);
                v_ngen_4437_ = leanh::lean_ctor_get(v___x_4434_, 2);
                v_auxDeclNGen_4438_ = leanh::lean_ctor_get(v___x_4434_, 3);
                v_traceState_4439_ = leanh::lean_ctor_get(v___x_4434_, 4);
                v_messages_4440_ = leanh::lean_ctor_get(v___x_4434_, 6);
                v_infoState_4441_ = leanh::lean_ctor_get(v___x_4434_, 7);
                v_snapshotTasks_4442_ = leanh::lean_ctor_get(v___x_4434_, 8);
                v_isSharedCheck_4470_ = (!leanh::lean_is_exclusive(v___x_4434_)) as u8;
                if v_isSharedCheck_4470_ == 0 {
                    v_unused_4471_ = leanh::lean_ctor_get(v___x_4434_, 5);
                    leanh::lean_dec(v_unused_4471_);
                    v___x_4444_ = v___x_4434_;
                    v_isShared_4445_ = v_isSharedCheck_4470_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4442_);
                    leanh::lean_inc(v_infoState_4441_);
                    leanh::lean_inc(v_messages_4440_);
                    leanh::lean_inc(v_traceState_4439_);
                    leanh::lean_inc(v_auxDeclNGen_4438_);
                    leanh::lean_inc(v_ngen_4437_);
                    leanh::lean_inc(v_nextMacroScope_4436_);
                    leanh::lean_inc(v_env_4435_);
                    leanh::lean_dec(v___x_4434_);
                    v___x_4444_ = leanh::lean_box(0);
                    v_isShared_4445_ = v_isSharedCheck_4470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4446_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__3_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__3,
                );
                v___x_4447_ = l_Lean_Kernel_setDiagnostics(v_env_4435_, v___x_4446_);
                v___x_4448_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__4_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__4,
                );
                if v_isShared_4445_ == 0 {
                    leanh::lean_ctor_set(v___x_4444_, 5, v___x_4448_);
                    leanh::lean_ctor_set(v___x_4444_, 0, v___x_4447_);
                    v___x_4450_ = v___x_4444_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 1, v_nextMacroScope_4436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 2, v_ngen_4437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 3, v_auxDeclNGen_4438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 4, v_traceState_4439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 5, v___x_4448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 6, v_messages_4440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 7, v_infoState_4441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 8, v_snapshotTasks_4442_);
                    v___x_4450_ = v_reuseFailAlloc_4469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4451_ = lean_st_ref_set(v___y_4421_, v___x_4450_);
                v___x_4452_ = lean_st_ref_take(v___y_4420_);
                v_mctx_4453_ = leanh::lean_ctor_get(v___x_4452_, 0);
                v_zetaDeltaFVarIds_4454_ = leanh::lean_ctor_get(v___x_4452_, 2);
                v_postponed_4455_ = leanh::lean_ctor_get(v___x_4452_, 3);
                v_diag_4456_ = leanh::lean_ctor_get(v___x_4452_, 4);
                v_isSharedCheck_4467_ = (!leanh::lean_is_exclusive(v___x_4452_)) as u8;
                if v_isSharedCheck_4467_ == 0 {
                    v_unused_4468_ = leanh::lean_ctor_get(v___x_4452_, 1);
                    leanh::lean_dec(v_unused_4468_);
                    v___x_4458_ = v___x_4452_;
                    v_isShared_4459_ = v_isSharedCheck_4467_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4456_);
                    leanh::lean_inc(v_postponed_4455_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4454_);
                    leanh::lean_inc(v_mctx_4453_);
                    leanh::lean_dec(v___x_4452_);
                    v___x_4458_ = leanh::lean_box(0);
                    v_isShared_4459_ = v_isSharedCheck_4467_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4460_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__5_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__5,
                );
                if v_isShared_4459_ == 0 {
                    leanh::lean_ctor_set(v___x_4458_, 1, v___x_4460_);
                    v___x_4462_ = v___x_4458_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_mctx_4453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 1, v___x_4460_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4466_,
                        2,
                        v_zetaDeltaFVarIds_4454_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 3, v_postponed_4455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 4, v_diag_4456_);
                    v___x_4462_ = v_reuseFailAlloc_4466_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4463_ = lean_st_ref_set(v___y_4420_, v___x_4462_);
                v___x_4464_ = leanh::lean_box(0);
                v___x_4465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4465_, 0, v___x_4464_);
                return v___x_4465_;
            }
            8 => {
                if v_isShared_4543_ == 0 {
                    v___x_4545_ = v___x_4542_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4546_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
                    v___x_4545_ = v_reuseFailAlloc_4546_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4545_;
            }
            10 => {
                if v_isShared_4551_ == 0 {
                    v___x_4553_ = v___x_4550_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
                    v___x_4553_ = v_reuseFailAlloc_4554_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4553_;
            }
            12 => {
                if v_isShared_4559_ == 0 {
                    v___x_4561_ = v___x_4558_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
                    v___x_4561_ = v_reuseFailAlloc_4562_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4561_;
            }
            14 => {
                if v_isShared_4567_ == 0 {
                    v___x_4569_ = v___x_4566_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
                    v___x_4569_ = v_reuseFailAlloc_4570_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4569_;
            }
            16 => {
                if v_isShared_4575_ == 0 {
                    v___x_4577_ = v___x_4574_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
                    v___x_4577_ = v_reuseFailAlloc_4578_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4577_;
            }
            18 => {
                if v_isShared_4583_ == 0 {
                    v___x_4585_ = v___x_4582_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
                    v___x_4585_ = v_reuseFailAlloc_4586_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4585_;
            }
            20 => {
                if v_isShared_4591_ == 0 {
                    v___x_4593_ = v___x_4590_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4594_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
                    v___x_4593_ = v_reuseFailAlloc_4594_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4593_;
            }
            22 => {
                if v_isShared_4599_ == 0 {
                    v___x_4601_ = v___x_4598_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
                    v___x_4601_ = v_reuseFailAlloc_4602_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reportDiag___lam__1___boxed(
    mut v_a_4604_: *mut leanh::LeanObject,
    mut v___f_4605_: *mut leanh::LeanObject,
    mut v___y_4606_: *mut leanh::LeanObject,
    mut v___y_4607_: *mut leanh::LeanObject,
    mut v___y_4608_: *mut leanh::LeanObject,
    mut v___y_4609_: *mut leanh::LeanObject,
    mut v___y_4610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_14165__boxed_4611_: u8 = 0;
    let mut v_res_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_14165__boxed_4611_ = (leanh::lean_unbox(v_a_4604_) as u8);
    v_res_4612_ = l_Lean_Meta_reportDiag___lam__1(
        v_a_14165__boxed_4611_,
        v___f_4605_,
        v___y_4606_,
        v___y_4607_,
        v___y_4608_,
        v___y_4609_,
    );
    leanh::lean_dec(v___y_4609_);
    leanh::lean_dec_ref(v___y_4608_);
    leanh::lean_dec(v___y_4607_);
    leanh::lean_dec_ref(v___y_4606_);
    return v_res_4612_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(
    mut v___y_4613_: *mut leanh::LeanObject,
    mut v_isExporting_4614_: u8,
    mut v___x_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
    mut v___x_4617_: *mut leanh::LeanObject,
    mut v_a_x3f_4618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4650_: u8 = 0;
    let mut v_unused_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4653_: u8 = 0;
    let mut v_unused_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4620_ = lean_st_ref_take(v___y_4613_);
                v_env_4621_ = leanh::lean_ctor_get(v___x_4620_, 0);
                v_nextMacroScope_4622_ = leanh::lean_ctor_get(v___x_4620_, 1);
                v_ngen_4623_ = leanh::lean_ctor_get(v___x_4620_, 2);
                v_auxDeclNGen_4624_ = leanh::lean_ctor_get(v___x_4620_, 3);
                v_traceState_4625_ = leanh::lean_ctor_get(v___x_4620_, 4);
                v_messages_4626_ = leanh::lean_ctor_get(v___x_4620_, 6);
                v_infoState_4627_ = leanh::lean_ctor_get(v___x_4620_, 7);
                v_snapshotTasks_4628_ = leanh::lean_ctor_get(v___x_4620_, 8);
                v_isSharedCheck_4653_ = (!leanh::lean_is_exclusive(v___x_4620_)) as u8;
                if v_isSharedCheck_4653_ == 0 {
                    v_unused_4654_ = leanh::lean_ctor_get(v___x_4620_, 5);
                    leanh::lean_dec(v_unused_4654_);
                    v___x_4630_ = v___x_4620_;
                    v_isShared_4631_ = v_isSharedCheck_4653_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4628_);
                    leanh::lean_inc(v_infoState_4627_);
                    leanh::lean_inc(v_messages_4626_);
                    leanh::lean_inc(v_traceState_4625_);
                    leanh::lean_inc(v_auxDeclNGen_4624_);
                    leanh::lean_inc(v_ngen_4623_);
                    leanh::lean_inc(v_nextMacroScope_4622_);
                    leanh::lean_inc(v_env_4621_);
                    leanh::lean_dec(v___x_4620_);
                    v___x_4630_ = leanh::lean_box(0);
                    v_isShared_4631_ = v_isSharedCheck_4653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4632_ = l_Lean_Environment_setExporting(v_env_4621_, v_isExporting_4614_);
                if v_isShared_4631_ == 0 {
                    leanh::lean_ctor_set(v___x_4630_, 5, v___x_4615_);
                    leanh::lean_ctor_set(v___x_4630_, 0, v___x_4632_);
                    v___x_4634_ = v___x_4630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4652_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 1, v_nextMacroScope_4622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 2, v_ngen_4623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 3, v_auxDeclNGen_4624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 4, v_traceState_4625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 5, v___x_4615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 6, v_messages_4626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 7, v_infoState_4627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 8, v_snapshotTasks_4628_);
                    v___x_4634_ = v_reuseFailAlloc_4652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4635_ = lean_st_ref_set(v___y_4613_, v___x_4634_);
                v___x_4636_ = lean_st_ref_take(v___y_4616_);
                v_mctx_4637_ = leanh::lean_ctor_get(v___x_4636_, 0);
                v_zetaDeltaFVarIds_4638_ = leanh::lean_ctor_get(v___x_4636_, 2);
                v_postponed_4639_ = leanh::lean_ctor_get(v___x_4636_, 3);
                v_diag_4640_ = leanh::lean_ctor_get(v___x_4636_, 4);
                v_isSharedCheck_4650_ = (!leanh::lean_is_exclusive(v___x_4636_)) as u8;
                if v_isSharedCheck_4650_ == 0 {
                    v_unused_4651_ = leanh::lean_ctor_get(v___x_4636_, 1);
                    leanh::lean_dec(v_unused_4651_);
                    v___x_4642_ = v___x_4636_;
                    v_isShared_4643_ = v_isSharedCheck_4650_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4640_);
                    leanh::lean_inc(v_postponed_4639_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4638_);
                    leanh::lean_inc(v_mctx_4637_);
                    leanh::lean_dec(v___x_4636_);
                    v___x_4642_ = leanh::lean_box(0);
                    v_isShared_4643_ = v_isSharedCheck_4650_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4643_ == 0 {
                    leanh::lean_ctor_set(v___x_4642_, 1, v___x_4617_);
                    v___x_4645_ = v___x_4642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4649_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_mctx_4637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 1, v___x_4617_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4649_,
                        2,
                        v_zetaDeltaFVarIds_4638_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 3, v_postponed_4639_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 4, v_diag_4640_);
                    v___x_4645_ = v_reuseFailAlloc_4649_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4646_ = lean_st_ref_set(v___y_4616_, v___x_4645_);
                v___x_4647_ = leanh::lean_box(0);
                v___x_4648_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4648_, 0, v___x_4647_);
                return v___x_4648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0___boxed(
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v_isExporting_4656_: *mut leanh::LeanObject,
    mut v___x_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
    mut v___x_4659_: *mut leanh::LeanObject,
    mut v_a_x3f_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4662_: u8 = 0;
    let mut v_res_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4662_ = (leanh::lean_unbox(v_isExporting_4656_) as u8);
    v_res_4663_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_4655_, v_isExporting_boxed_4662_, v___x_4657_, v___y_4658_, v___x_4659_, v_a_x3f_4660_);
    leanh::lean_dec(v_a_x3f_4660_);
    leanh::lean_dec(v___y_4658_);
    leanh::lean_dec(v___y_4655_);
    return v_res_4663_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4664_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4665_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0);
    v___x_4666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4666_, 0, v___x_4665_);
    return v___x_4666_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1);
    v___x_4668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4668_, 0, v___x_4667_);
    leanh::lean_ctor_set(v___x_4668_, 1, v___x_4667_);
    return v___x_4668_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4669_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1);
    v___x_4670_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_4670_, 0, v___x_4669_);
    leanh::lean_ctor_set(v___x_4670_, 1, v___x_4669_);
    leanh::lean_ctor_set(v___x_4670_, 2, v___x_4669_);
    leanh::lean_ctor_set(v___x_4670_, 3, v___x_4669_);
    leanh::lean_ctor_set(v___x_4670_, 4, v___x_4669_);
    leanh::lean_ctor_set(v___x_4670_, 5, v___x_4669_);
    return v___x_4670_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(
    mut v_x_4671_: *mut leanh::LeanObject,
    mut v_isExporting_4672_: u8,
    mut v___y_4673_: *mut leanh::LeanObject,
    mut v___y_4674_: *mut leanh::LeanObject,
    mut v___y_4675_: *mut leanh::LeanObject,
    mut v___y_4676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4680_: u8 = 0;
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4692_: u8 = 0;
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4705_: u8 = 0;
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4714_: u8 = 0;
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut v_unused_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4727_: u8 = 0;
    let mut v_a_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v_unused_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_unused_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4743_: u8 = 0;
    let mut v_unused_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4678_ = lean_st_ref_get(v___y_4676_);
                v_env_4679_ = leanh::lean_ctor_get(v___x_4678_, 0);
                leanh::lean_inc_ref(v_env_4679_);
                leanh::lean_dec(v___x_4678_);
                v_isExporting_4680_ = leanh::lean_ctor_get_uint8(
                    v_env_4679_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_4679_);
                v___x_4681_ = lean_st_ref_take(v___y_4676_);
                v_env_4682_ = leanh::lean_ctor_get(v___x_4681_, 0);
                v_nextMacroScope_4683_ = leanh::lean_ctor_get(v___x_4681_, 1);
                v_ngen_4684_ = leanh::lean_ctor_get(v___x_4681_, 2);
                v_auxDeclNGen_4685_ = leanh::lean_ctor_get(v___x_4681_, 3);
                v_traceState_4686_ = leanh::lean_ctor_get(v___x_4681_, 4);
                v_messages_4687_ = leanh::lean_ctor_get(v___x_4681_, 6);
                v_infoState_4688_ = leanh::lean_ctor_get(v___x_4681_, 7);
                v_snapshotTasks_4689_ = leanh::lean_ctor_get(v___x_4681_, 8);
                v_isSharedCheck_4743_ = (!leanh::lean_is_exclusive(v___x_4681_)) as u8;
                if v_isSharedCheck_4743_ == 0 {
                    v_unused_4744_ = leanh::lean_ctor_get(v___x_4681_, 5);
                    leanh::lean_dec(v_unused_4744_);
                    v___x_4691_ = v___x_4681_;
                    v_isShared_4692_ = v_isSharedCheck_4743_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4689_);
                    leanh::lean_inc(v_infoState_4688_);
                    leanh::lean_inc(v_messages_4687_);
                    leanh::lean_inc(v_traceState_4686_);
                    leanh::lean_inc(v_auxDeclNGen_4685_);
                    leanh::lean_inc(v_ngen_4684_);
                    leanh::lean_inc(v_nextMacroScope_4683_);
                    leanh::lean_inc(v_env_4682_);
                    leanh::lean_dec(v___x_4681_);
                    v___x_4691_ = leanh::lean_box(0);
                    v_isShared_4692_ = v_isSharedCheck_4743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4693_ = l_Lean_Environment_setExporting(v_env_4682_, v_isExporting_4672_);
                v___x_4694_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2);
                if v_isShared_4692_ == 0 {
                    leanh::lean_ctor_set(v___x_4691_, 5, v___x_4694_);
                    leanh::lean_ctor_set(v___x_4691_, 0, v___x_4693_);
                    v___x_4696_ = v___x_4691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4742_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_nextMacroScope_4683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 2, v_ngen_4684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 3, v_auxDeclNGen_4685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 4, v_traceState_4686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 5, v___x_4694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 6, v_messages_4687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 7, v_infoState_4688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4742_, 8, v_snapshotTasks_4689_);
                    v___x_4696_ = v_reuseFailAlloc_4742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4697_ = lean_st_ref_set(v___y_4676_, v___x_4696_);
                v___x_4698_ = lean_st_ref_take(v___y_4674_);
                v_mctx_4699_ = leanh::lean_ctor_get(v___x_4698_, 0);
                v_zetaDeltaFVarIds_4700_ = leanh::lean_ctor_get(v___x_4698_, 2);
                v_postponed_4701_ = leanh::lean_ctor_get(v___x_4698_, 3);
                v_diag_4702_ = leanh::lean_ctor_get(v___x_4698_, 4);
                v_isSharedCheck_4740_ = (!leanh::lean_is_exclusive(v___x_4698_)) as u8;
                if v_isSharedCheck_4740_ == 0 {
                    v_unused_4741_ = leanh::lean_ctor_get(v___x_4698_, 1);
                    leanh::lean_dec(v_unused_4741_);
                    v___x_4704_ = v___x_4698_;
                    v_isShared_4705_ = v_isSharedCheck_4740_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4702_);
                    leanh::lean_inc(v_postponed_4701_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4700_);
                    leanh::lean_inc(v_mctx_4699_);
                    leanh::lean_dec(v___x_4698_);
                    v___x_4704_ = leanh::lean_box(0);
                    v_isShared_4705_ = v_isSharedCheck_4740_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4706_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3);
                if v_isShared_4705_ == 0 {
                    leanh::lean_ctor_set(v___x_4704_, 1, v___x_4706_);
                    v___x_4708_ = v___x_4704_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_mctx_4699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 1, v___x_4706_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4739_,
                        2,
                        v_zetaDeltaFVarIds_4700_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 3, v_postponed_4701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 4, v_diag_4702_);
                    v___x_4708_ = v_reuseFailAlloc_4739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4709_ = lean_st_ref_set(v___y_4674_, v___x_4708_);
                leanh::lean_inc(v___y_4676_);
                leanh::lean_inc_ref(v___y_4675_);
                leanh::lean_inc(v___y_4674_);
                leanh::lean_inc_ref(v___y_4673_);
                v_r_4710_ = leanh::lean_apply_5(
                    v_x_4671_,
                    v___y_4673_,
                    v___y_4674_,
                    v___y_4675_,
                    v___y_4676_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_4710_) == 0 {
                    v_a_4711_ = leanh::lean_ctor_get(v_r_4710_, 0);
                    v_isSharedCheck_4727_ = (!leanh::lean_is_exclusive(v_r_4710_)) as u8;
                    if v_isSharedCheck_4727_ == 0 {
                        v___x_4713_ = v_r_4710_;
                        v_isShared_4714_ = v_isSharedCheck_4727_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4711_);
                        leanh::lean_dec(v_r_4710_);
                        v___x_4713_ = leanh::lean_box(0);
                        v_isShared_4714_ = v_isSharedCheck_4727_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_4728_ = leanh::lean_ctor_get(v_r_4710_, 0);
                    leanh::lean_inc(v_a_4728_);
                    leanh::lean_dec_ref_known(v_r_4710_, 1);
                    v___x_4729_ = leanh::lean_box(0);
                    v___x_4730_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_4676_, v_isExporting_4680_, v___x_4694_, v___y_4674_, v___x_4706_, v___x_4729_);
                    v_isSharedCheck_4737_ = (!leanh::lean_is_exclusive(v___x_4730_)) as u8;
                    if v_isSharedCheck_4737_ == 0 {
                        v_unused_4738_ = leanh::lean_ctor_get(v___x_4730_, 0);
                        leanh::lean_dec(v_unused_4738_);
                        v___x_4732_ = v___x_4730_;
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4730_);
                        v___x_4732_ = leanh::lean_box(0);
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_4711_);
                if v_isShared_4714_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4713_, 1);
                    v___x_4716_ = v___x_4713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4726_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4711_);
                    v___x_4716_ = v_reuseFailAlloc_4726_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4717_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_4676_, v_isExporting_4680_, v___x_4694_, v___y_4674_, v___x_4706_, v___x_4716_);
                leanh::lean_dec_ref(v___x_4716_);
                v_isSharedCheck_4724_ = (!leanh::lean_is_exclusive(v___x_4717_)) as u8;
                if v_isSharedCheck_4724_ == 0 {
                    v_unused_4725_ = leanh::lean_ctor_get(v___x_4717_, 0);
                    leanh::lean_dec(v_unused_4725_);
                    v___x_4719_ = v___x_4717_;
                    v_isShared_4720_ = v_isSharedCheck_4724_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4717_);
                    v___x_4719_ = leanh::lean_box(0);
                    v_isShared_4720_ = v_isSharedCheck_4724_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4720_ == 0 {
                    leanh::lean_ctor_set(v___x_4719_, 0, v_a_4711_);
                    v___x_4722_ = v___x_4719_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4723_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4711_);
                    v___x_4722_ = v_reuseFailAlloc_4723_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4722_;
            }
            9 => {
                if v_isShared_4733_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4732_, 1);
                    leanh::lean_ctor_set(v___x_4732_, 0, v_a_4728_);
                    v___x_4735_ = v___x_4732_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4728_);
                    v___x_4735_ = v_reuseFailAlloc_4736_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___boxed(
    mut v_x_4745_: *mut leanh::LeanObject,
    mut v_isExporting_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
    mut v___y_4749_: *mut leanh::LeanObject,
    mut v___y_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4752_: u8 = 0;
    let mut v_res_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4752_ = (leanh::lean_unbox(v_isExporting_4746_) as u8);
    v_res_4753_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(v_x_4745_, v_isExporting_boxed_4752_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
    leanh::lean_dec(v___y_4750_);
    leanh::lean_dec_ref(v___y_4749_);
    leanh::lean_dec(v___y_4748_);
    leanh::lean_dec_ref(v___y_4747_);
    return v_res_4753_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg(
    mut v_x_4754_: *mut leanh::LeanObject,
    mut v_when_4755_: u8,
    mut v___y_4756_: *mut leanh::LeanObject,
    mut v___y_4757_: *mut leanh::LeanObject,
    mut v___y_4758_: *mut leanh::LeanObject,
    mut v___y_4759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_4755_ == 0 {
        let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_4759_);
        leanh::lean_inc_ref(v___y_4758_);
        leanh::lean_inc(v___y_4757_);
        leanh::lean_inc_ref(v___y_4756_);
        v___x_4761_ = leanh::lean_apply_5(
            v_x_4754_,
            v___y_4756_,
            v___y_4757_,
            v___y_4758_,
            v___y_4759_,
            leanh::lean_box(0),
        );
        return v___x_4761_;
    } else {
        let mut v___x_4762_: u8 = 0;
        let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4762_ = 0;
        v___x_4763_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(v_x_4754_, v___x_4762_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
        return v___x_4763_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg___boxed(
    mut v_x_4764_: *mut leanh::LeanObject,
    mut v_when_4765_: *mut leanh::LeanObject,
    mut v___y_4766_: *mut leanh::LeanObject,
    mut v___y_4767_: *mut leanh::LeanObject,
    mut v___y_4768_: *mut leanh::LeanObject,
    mut v___y_4769_: *mut leanh::LeanObject,
    mut v___y_4770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_4771_: u8 = 0;
    let mut v_res_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4771_ = (leanh::lean_unbox(v_when_4765_) as u8);
    v_res_4772_ = l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg(
        v_x_4764_,
        v_when_boxed_4771_,
        v___y_4766_,
        v___y_4767_,
        v___y_4768_,
        v___y_4769_,
    );
    leanh::lean_dec(v___y_4769_);
    leanh::lean_dec_ref(v___y_4768_);
    leanh::lean_dec(v___y_4767_);
    leanh::lean_dec_ref(v___y_4766_);
    return v_res_4772_;
}
pub unsafe fn l_Lean_Meta_reportDiag(
    mut v_a_4773_: *mut leanh::LeanObject,
    mut v_a_4774_: *mut leanh::LeanObject,
    mut v_a_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: u8 = 0;
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4792_: u8 = 0;
    let mut v_a_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4778_ = l_Lean_isDiagnosticsEnabled___redArg(v_a_4775_);
                if leanh::lean_obj_tag(v___x_4778_) == 0 {
                    v_a_4779_ = leanh::lean_ctor_get(v___x_4778_, 0);
                    v_isSharedCheck_4792_ = (!leanh::lean_is_exclusive(v___x_4778_)) as u8;
                    if v_isSharedCheck_4792_ == 0 {
                        v___x_4781_ = v___x_4778_;
                        v_isShared_4782_ = v_isSharedCheck_4792_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4779_);
                        leanh::lean_dec(v___x_4778_);
                        v___x_4781_ = leanh::lean_box(0);
                        v_isShared_4782_ = v_isSharedCheck_4792_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4793_ = leanh::lean_ctor_get(v___x_4778_, 0);
                    v_isSharedCheck_4800_ = (!leanh::lean_is_exclusive(v___x_4778_)) as u8;
                    if v_isSharedCheck_4800_ == 0 {
                        v___x_4795_ = v___x_4778_;
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4793_);
                        leanh::lean_dec(v___x_4778_);
                        v___x_4795_ = leanh::lean_box(0);
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4783_ = (leanh::lean_unbox(v_a_4779_) as u8);
                if v___x_4783_ == 0 {
                    leanh::lean_dec(v_a_4779_);
                    v___x_4784_ = leanh::lean_box(0);
                    if v_isShared_4782_ == 0 {
                        leanh::lean_ctor_set(v___x_4781_, 0, v___x_4784_);
                        v___x_4786_ = v___x_4781_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
                        v___x_4786_ = v_reuseFailAlloc_4787_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4781_);
                    leanh::lean_inc_n(v_a_4779_, 2);
                    v___f_4788_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_reportDiag___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_4788_, 0, v_a_4779_);
                    v___f_4789_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_reportDiag___lam__1___boxed as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    leanh::lean_closure_set(v___f_4789_, 0, v_a_4779_);
                    leanh::lean_closure_set(v___f_4789_, 1, v___f_4788_);
                    v___x_4790_ = (leanh::lean_unbox(v_a_4779_) as u8);
                    leanh::lean_dec(v_a_4779_);
                    v___x_4791_ =
                        l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg(
                            v___f_4789_,
                            v___x_4790_,
                            v_a_4773_,
                            v_a_4774_,
                            v_a_4775_,
                            v_a_4776_,
                        );
                    return v___x_4791_;
                }
            }
            2 => {
                return v___x_4786_;
            }
            3 => {
                if v_isShared_4796_ == 0 {
                    v___x_4798_ = v___x_4795_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
                    v___x_4798_ = v_reuseFailAlloc_4799_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reportDiag___boxed(
    mut v_a_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
    mut v_a_4805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4806_ = l_Lean_Meta_reportDiag(v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
    leanh::lean_dec(v_a_4804_);
    leanh::lean_dec_ref(v_a_4803_);
    leanh::lean_dec(v_a_4802_);
    leanh::lean_dec_ref(v_a_4801_);
    return v_res_4806_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2(
    mut v_00_u03b1_4807_: *mut leanh::LeanObject,
    mut v_x_4808_: *mut leanh::LeanObject,
    mut v_isExporting_4809_: u8,
    mut v___y_4810_: *mut leanh::LeanObject,
    mut v___y_4811_: *mut leanh::LeanObject,
    mut v___y_4812_: *mut leanh::LeanObject,
    mut v___y_4813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4815_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(v_x_4808_, v_isExporting_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
    return v___x_4815_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___boxed(
    mut v_00_u03b1_4816_: *mut leanh::LeanObject,
    mut v_x_4817_: *mut leanh::LeanObject,
    mut v_isExporting_4818_: *mut leanh::LeanObject,
    mut v___y_4819_: *mut leanh::LeanObject,
    mut v___y_4820_: *mut leanh::LeanObject,
    mut v___y_4821_: *mut leanh::LeanObject,
    mut v___y_4822_: *mut leanh::LeanObject,
    mut v___y_4823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4824_: u8 = 0;
    let mut v_res_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4824_ = (leanh::lean_unbox(v_isExporting_4818_) as u8);
    v_res_4825_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2(v_00_u03b1_4816_, v_x_4817_, v_isExporting_boxed_4824_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
    leanh::lean_dec(v___y_4822_);
    leanh::lean_dec_ref(v___y_4821_);
    leanh::lean_dec(v___y_4820_);
    leanh::lean_dec_ref(v___y_4819_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1(
    mut v_00_u03b1_4826_: *mut leanh::LeanObject,
    mut v_x_4827_: *mut leanh::LeanObject,
    mut v_when_4828_: u8,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
    mut v___y_4831_: *mut leanh::LeanObject,
    mut v___y_4832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4834_ = l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg(
        v_x_4827_,
        v_when_4828_,
        v___y_4829_,
        v___y_4830_,
        v___y_4831_,
        v___y_4832_,
    );
    return v___x_4834_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___boxed(
    mut v_00_u03b1_4835_: *mut leanh::LeanObject,
    mut v_x_4836_: *mut leanh::LeanObject,
    mut v_when_4837_: *mut leanh::LeanObject,
    mut v___y_4838_: *mut leanh::LeanObject,
    mut v___y_4839_: *mut leanh::LeanObject,
    mut v___y_4840_: *mut leanh::LeanObject,
    mut v___y_4841_: *mut leanh::LeanObject,
    mut v___y_4842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_4843_: u8 = 0;
    let mut v_res_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4843_ = (leanh::lean_unbox(v_when_4837_) as u8);
    v_res_4844_ = l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1(
        v_00_u03b1_4835_,
        v_x_4836_,
        v_when_boxed_4843_,
        v___y_4838_,
        v___y_4839_,
        v___y_4840_,
        v___y_4841_,
    );
    leanh::lean_dec(v___y_4841_);
    leanh::lean_dec_ref(v___y_4840_);
    leanh::lean_dec(v___y_4839_);
    leanh::lean_dec_ref(v___y_4838_);
    return v_res_4844_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Diagnostics(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Diagnostics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Diagnostics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Diagnostics(builtin);
}