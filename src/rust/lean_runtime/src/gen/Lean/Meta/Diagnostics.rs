// Lean compiler output
// Module: Lean.Meta.Diagnostics
// Imports: Lean.Meta.Basic Lean.PrettyPrinter
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
    l_Lean_Name_mkStr1, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_5, lean_apply_7, lean_apply_8, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_collectAboveThreshold___redArg___closed__10_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_collectAboveThreshold___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___redArg___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_subCounters___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_subCounters___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_subCounters___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_subCounters___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_instInhabitedDiagSummary_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instInhabitedDiagSummary_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedDiagSummary_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedDiagSummary: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSummary___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_lt___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_mkDiagSummary___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummary___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSummary___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkDiagSummary___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummary___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUnfolded___closed__0_value)
                as *mut LeanObject,
            16626236724633252301 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1_value)
                as *mut LeanObject,
            9097021930341754798 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_mkDiagSynthPendingFailure___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_mkDiagSynthPendingFailure___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instInhabitedDiagSummary_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_mkDiagSynthPendingFailure___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkDiagSynthPendingFailure___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_appendSection___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_appendSection___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_appendSection___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_appendSection___closed__1_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_appendSection___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_appendSection___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_appendSection___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_appendSection___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_appendSection___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_reportDiag___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_reportDiag___lam__1___closed__6_value: LeanStringObject<7> =
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
        m_data: [100, 101, 102, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__6_value) as *mut LeanObject,
        10404218160629279456 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__8_value: LeanStringObject<7> =
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
        m_data: [107, 101, 114, 110, 101, 108, 0],
    };
static mut l_Lean_Meta_reportDiag___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__8_value) as *mut LeanObject,
        4997480113592071246 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__10_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__11_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__12_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__13_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__14_value: LeanStringObject<51> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__15_value: LeanStringObject<49> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__15_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__16_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__16_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__17_value: LeanStringObject<75> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__17_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__18_value: LeanStringObject<89> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__18_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__19_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__19_value) as *mut LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_reportDiag___lam__1___closed__21_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__21_value) as *mut LeanObject,
        2816192749436305809 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__22_value) as *mut LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_reportDiag___lam__1___closed__24_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_reportDiag___lam__1___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__24_value) as *mut LeanObject;
pub static l_Lean_Meta_reportDiag___lam__1___closed__25_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__24_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_reportDiag___lam__1___closed__25_value) as *mut LeanObject;
static mut l_Lean_Meta_reportDiag___lam__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_reportDiag___lam__1___closed__26: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__0(
    mut v_threshold_2423_: *mut LeanObject,
    mut v_p_2424_: *mut LeanObject,
    mut v_x_2425_: *mut LeanObject,
    mut v_____s_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    v_fst_2427_ = lean_ctor_get(v_x_2425_, 0);
    v_snd_2428_ = lean_ctor_get(v_x_2425_, 1);
    v___x_2429_ = lean_nat_dec_lt(v_threshold_2423_, v_snd_2428_);
    if v___x_2429_ == 0 {
        let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_2425_);
        lean_dec_ref(v_p_2424_);
        v___x_2430_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2430_, 0, v_____s_2426_);
        return v___x_2430_;
    } else {
        let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2432_: u8 = 0;
        lean_inc(v_fst_2427_);
        v___x_2431_ = lean_apply_1(v_p_2424_, v_fst_2427_);
        v___x_2432_ = (lean_unbox(v___x_2431_) as u8);
        if v___x_2432_ == 0 {
            let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_x_2425_);
            v___x_2433_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_2433_, 0, v_____s_2426_);
            return v___x_2433_;
        } else {
            let mut v_r_2434_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
            v_r_2434_ = lean_array_push(v_____s_2426_, v_x_2425_);
            v___x_2435_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_2435_, 0, v_r_2434_);
            return v___x_2435_;
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__0___boxed(
    mut v_threshold_2436_: *mut LeanObject,
    mut v_p_2437_: *mut LeanObject,
    mut v_x_2438_: *mut LeanObject,
    mut v_____s_2439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2440_: *mut LeanObject = core::ptr::null_mut();
    v_res_2440_ = l_Lean_Meta_collectAboveThreshold___redArg___lam__0(
        v_threshold_2436_,
        v_p_2437_,
        v_x_2438_,
        v_____s_2439_,
    );
    lean_dec(v_threshold_2436_);
    return v_res_2440_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__1(
    mut v_lt_2441_: *mut LeanObject,
    mut v_x_2442_: *mut LeanObject,
    mut v_x_2443_: *mut LeanObject,
) -> u8 {
    let mut v_fst_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: u8 = 0;
    v_fst_2444_ = lean_ctor_get(v_x_2442_, 0);
    lean_inc(v_fst_2444_);
    v_snd_2445_ = lean_ctor_get(v_x_2442_, 1);
    lean_inc(v_snd_2445_);
    lean_dec_ref(v_x_2442_);
    v_fst_2446_ = lean_ctor_get(v_x_2443_, 0);
    lean_inc(v_fst_2446_);
    v_snd_2447_ = lean_ctor_get(v_x_2443_, 1);
    lean_inc(v_snd_2447_);
    lean_dec_ref(v_x_2443_);
    v___x_2448_ = lean_nat_dec_eq(v_snd_2445_, v_snd_2447_);
    if v___x_2448_ == 0 {
        let mut v___x_2449_: u8 = 0;
        lean_dec(v_fst_2446_);
        lean_dec(v_fst_2444_);
        lean_dec_ref(v_lt_2441_);
        v___x_2449_ = lean_nat_dec_lt(v_snd_2447_, v_snd_2445_);
        lean_dec(v_snd_2445_);
        lean_dec(v_snd_2447_);
        return v___x_2449_;
    } else {
        let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: u8 = 0;
        lean_dec(v_snd_2447_);
        lean_dec(v_snd_2445_);
        v___x_2450_ = lean_apply_2(v_lt_2441_, v_fst_2444_, v_fst_2446_);
        v___x_2451_ = (lean_unbox(v___x_2450_) as u8);
        return v___x_2451_;
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___lam__1___boxed(
    mut v_lt_2452_: *mut LeanObject,
    mut v_x_2453_: *mut LeanObject,
    mut v_x_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2455_: u8 = 0;
    let mut v_r_2456_: *mut LeanObject = core::ptr::null_mut();
    v_res_2455_ =
        l_Lean_Meta_collectAboveThreshold___redArg___lam__1(v_lt_2452_, v_x_2453_, v_x_2454_);
    v_r_2456_ = lean_box((v_res_2455_) as usize);
    return v_r_2456_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg(
    mut v_counters_2478_: *mut LeanObject,
    mut v_threshold_2479_: *mut LeanObject,
    mut v_p_2480_: *mut LeanObject,
    mut v_lt_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v___f_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: u8 = 0;
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2482_ = lean_alloc_closure(
                    l_Lean_Meta_collectAboveThreshold___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_2482_, 0, v_threshold_2479_);
                lean_closure_set(v___f_2482_, 1, v_p_2480_);
                v___x_2483_ = l_Lean_Meta_collectAboveThreshold___redArg___closed__9;
                v___x_2484_ = lean_unsigned_to_nat(0);
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
                    v___f_2489_ = lean_alloc_closure(
                        l_Lean_Meta_collectAboveThreshold___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_2489_, 0, v_lt_2481_);
                    v___x_2490_ = lean_unsigned_to_nat(1);
                    v___x_2491_ = lean_nat_sub(v___x_2487_, v___x_2490_);
                    v___x_2497_ = lean_nat_dec_le(v___x_2484_, v___x_2491_);
                    if v___x_2497_ == 0 {
                        lean_inc(v___x_2491_);
                        v___y_2493_ = v___x_2491_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2493_ = v___x_2484_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_lt_2481_);
                    return v___x_2486_;
                }
            }
            1 => {
                v___x_2494_ = lean_nat_dec_le(v___y_2493_, v___x_2491_);
                if v___x_2494_ == 0 {
                    lean_dec(v___x_2491_);
                    lean_inc(v___y_2493_);
                    v___x_2495_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        lean_box(0),
                        v___f_2489_,
                        v___x_2487_,
                        v___x_2486_,
                        v___y_2493_,
                        v___y_2493_,
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                    );
                    lean_dec(v___y_2493_);
                    return v___x_2495_;
                } else {
                    v___x_2496_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        lean_box(0),
                        v___f_2489_,
                        v___x_2487_,
                        v___x_2486_,
                        v___y_2493_,
                        v___x_2491_,
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                    );
                    lean_dec(v___x_2491_);
                    return v___x_2496_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___redArg___boxed(
    mut v_counters_2498_: *mut LeanObject,
    mut v_threshold_2499_: *mut LeanObject,
    mut v_p_2500_: *mut LeanObject,
    mut v_lt_2501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2502_: *mut LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Lean_Meta_collectAboveThreshold___redArg(
        v_counters_2498_,
        v_threshold_2499_,
        v_p_2500_,
        v_lt_2501_,
    );
    lean_dec_ref(v_counters_2498_);
    return v_res_2502_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold(
    mut v_00_u03b1_2503_: *mut LeanObject,
    mut v_inst_2504_: *mut LeanObject,
    mut v_inst_2505_: *mut LeanObject,
    mut v_counters_2506_: *mut LeanObject,
    mut v_threshold_2507_: *mut LeanObject,
    mut v_p_2508_: *mut LeanObject,
    mut v_lt_2509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    v___x_2510_ = l_Lean_Meta_collectAboveThreshold___redArg(
        v_counters_2506_,
        v_threshold_2507_,
        v_p_2508_,
        v_lt_2509_,
    );
    return v___x_2510_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___boxed(
    mut v_00_u03b1_2511_: *mut LeanObject,
    mut v_inst_2512_: *mut LeanObject,
    mut v_inst_2513_: *mut LeanObject,
    mut v_counters_2514_: *mut LeanObject,
    mut v_threshold_2515_: *mut LeanObject,
    mut v_p_2516_: *mut LeanObject,
    mut v_lt_2517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2518_: *mut LeanObject = core::ptr::null_mut();
    v_res_2518_ = l_Lean_Meta_collectAboveThreshold(
        v_00_u03b1_2511_,
        v_inst_2512_,
        v_inst_2513_,
        v_counters_2514_,
        v_threshold_2515_,
        v_p_2516_,
        v_lt_2517_,
    );
    lean_dec_ref(v_counters_2514_);
    lean_dec_ref(v_inst_2513_);
    lean_dec_ref(v_inst_2512_);
    return v_res_2518_;
}
pub unsafe fn l_Lean_Meta_subCounters___redArg___lam__0(
    mut v_inst_2519_: *mut LeanObject,
    mut v_inst_2520_: *mut LeanObject,
    mut v_oldCounters_2521_: *mut LeanObject,
    mut v_x_2522_: *mut LeanObject,
    mut v_____s_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v_result_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2524_ = lean_ctor_get(v_x_2522_, 0);
                lean_inc_n(v_fst_2524_, 2);
                v_snd_2525_ = lean_ctor_get(v_x_2522_, 1);
                lean_inc(v_snd_2525_);
                lean_dec_ref(v_x_2522_);
                lean_inc_ref(v_inst_2520_);
                lean_inc_ref(v_inst_2519_);
                v___x_2526_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v_inst_2519_,
                    v_inst_2520_,
                    v_oldCounters_2521_,
                    v_fst_2524_,
                );
                if lean_obj_tag(v___x_2526_) == 1 {
                    v_val_2527_ = lean_ctor_get(v___x_2526_, 0);
                    v_isSharedCheck_2536_ = (!lean_is_exclusive(v___x_2526_)) as u8;
                    if v_isSharedCheck_2536_ == 0 {
                        v___x_2529_ = v___x_2526_;
                        v_isShared_2530_ = v_isSharedCheck_2536_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2527_);
                        lean_dec(v___x_2526_);
                        v___x_2529_ = lean_box(0);
                        v_isShared_2530_ = v_isSharedCheck_2536_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2526_);
                    v_result_2537_ = l_Lean_PersistentHashMap_insert___redArg(
                        v_inst_2519_,
                        v_inst_2520_,
                        v_____s_2523_,
                        v_fst_2524_,
                        v_snd_2525_,
                    );
                    v___x_2538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2538_, 0, v_result_2537_);
                    return v___x_2538_;
                }
            }
            1 => {
                v___x_2531_ = lean_nat_sub(v_snd_2525_, v_val_2527_);
                lean_dec(v_val_2527_);
                lean_dec(v_snd_2525_);
                v_result_2532_ = l_Lean_PersistentHashMap_insert___redArg(
                    v_inst_2519_,
                    v_inst_2520_,
                    v_____s_2523_,
                    v_fst_2524_,
                    v___x_2531_,
                );
                if v_isShared_2530_ == 0 {
                    lean_ctor_set(v___x_2529_, 0, v_result_2532_);
                    v___x_2534_ = v___x_2529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_result_2532_);
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
    mut v_inst_2539_: *mut LeanObject,
    mut v_inst_2540_: *mut LeanObject,
    mut v_oldCounters_2541_: *mut LeanObject,
    mut v_x_2542_: *mut LeanObject,
    mut v_____s_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2544_: *mut LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_Lean_Meta_subCounters___redArg___lam__0(
        v_inst_2539_,
        v_inst_2540_,
        v_oldCounters_2541_,
        v_x_2542_,
        v_____s_2543_,
    );
    lean_dec_ref(v_oldCounters_2541_);
    return v_res_2544_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    v___x_2545_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2545_;
}
pub unsafe fn _init_l_Lean_Meta_subCounters___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_2547_: *mut LeanObject = core::ptr::null_mut();
    v___x_2546_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_subCounters___redArg___closed__0_once),
        _init_l_Lean_Meta_subCounters___redArg___closed__0,
    );
    v_result_2547_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v_result_2547_, 0, v___x_2546_);
    return v_result_2547_;
}
pub unsafe fn l_Lean_Meta_subCounters___redArg(
    mut v_inst_2548_: *mut LeanObject,
    mut v_inst_2549_: *mut LeanObject,
    mut v_newCounters_2550_: *mut LeanObject,
    mut v_oldCounters_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    v___f_2552_ = lean_alloc_closure(
        l_Lean_Meta_subCounters___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2552_, 0, v_inst_2548_);
    lean_closure_set(v___f_2552_, 1, v_inst_2549_);
    lean_closure_set(v___f_2552_, 2, v_oldCounters_2551_);
    v___x_2553_ = l_Lean_Meta_collectAboveThreshold___redArg___closed__9;
    v_result_2554_ = lean_obj_once(
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
    mut v_inst_2556_: *mut LeanObject,
    mut v_inst_2557_: *mut LeanObject,
    mut v_newCounters_2558_: *mut LeanObject,
    mut v_oldCounters_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2560_: *mut LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_Lean_Meta_subCounters___redArg(
        v_inst_2556_,
        v_inst_2557_,
        v_newCounters_2558_,
        v_oldCounters_2559_,
    );
    lean_dec_ref(v_newCounters_2558_);
    return v_res_2560_;
}
pub unsafe fn l_Lean_Meta_subCounters(
    mut v_00_u03b1_2561_: *mut LeanObject,
    mut v_inst_2562_: *mut LeanObject,
    mut v_inst_2563_: *mut LeanObject,
    mut v_newCounters_2564_: *mut LeanObject,
    mut v_oldCounters_2565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Lean_Meta_subCounters___redArg(
        v_inst_2562_,
        v_inst_2563_,
        v_newCounters_2564_,
        v_oldCounters_2565_,
    );
    return v___x_2566_;
}
pub unsafe fn l_Lean_Meta_subCounters___boxed(
    mut v_00_u03b1_2567_: *mut LeanObject,
    mut v_inst_2568_: *mut LeanObject,
    mut v_inst_2569_: *mut LeanObject,
    mut v_newCounters_2570_: *mut LeanObject,
    mut v_oldCounters_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2572_: *mut LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Lean_Meta_subCounters(
        v_00_u03b1_2567_,
        v_inst_2568_,
        v_inst_2569_,
        v_newCounters_2570_,
        v_oldCounters_2571_,
    );
    lean_dec_ref(v_newCounters_2570_);
    return v_res_2572_;
}
pub unsafe fn l_Lean_Meta_DiagSummary_isEmpty(mut v_s_2580_: *mut LeanObject) -> u8 {
    let mut v_data_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: u8 = 0;
    v_data_2581_ = lean_ctor_get(v_s_2580_, 0);
    v___x_2582_ = lean_array_get_size(v_data_2581_);
    v___x_2583_ = lean_unsigned_to_nat(0);
    v___x_2584_ = lean_nat_dec_eq(v___x_2582_, v___x_2583_);
    return v___x_2584_;
}
pub unsafe fn l_Lean_Meta_DiagSummary_isEmpty___boxed(
    mut v_s_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2586_: u8 = 0;
    let mut v_r_2587_: *mut LeanObject = core::ptr::null_mut();
    v_res_2586_ = l_Lean_Meta_DiagSummary_isEmpty(v_s_2585_);
    lean_dec_ref(v_s_2585_);
    v_r_2587_ = lean_box((v_res_2586_) as usize);
    return v_r_2587_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0(
    mut v_opts_2588_: *mut LeanObject,
    mut v_opt_2589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    v_name_2590_ = lean_ctor_get(v_opt_2589_, 0);
    v_defValue_2591_ = lean_ctor_get(v_opt_2589_, 1);
    v_map_2592_ = lean_ctor_get(v_opts_2588_, 0);
    v___x_2593_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2592_,
            v_name_2590_,
        );
    if lean_obj_tag(v___x_2593_) == 0 {
        lean_inc(v_defValue_2591_);
        return v_defValue_2591_;
    } else {
        let mut v_val_2594_: *mut LeanObject = core::ptr::null_mut();
        v_val_2594_ = lean_ctor_get(v___x_2593_, 0);
        lean_inc(v_val_2594_);
        lean_dec_ref_known(v___x_2593_, 1);
        if lean_obj_tag(v_val_2594_) == 3 {
            let mut v_v_2595_: *mut LeanObject = core::ptr::null_mut();
            v_v_2595_ = lean_ctor_get(v_val_2594_, 0);
            lean_inc(v_v_2595_);
            lean_dec_ref_known(v_val_2594_, 1);
            return v_v_2595_;
        } else {
            lean_dec(v_val_2594_);
            lean_inc(v_defValue_2591_);
            return v_defValue_2591_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0___boxed(
    mut v_opts_2596_: *mut LeanObject,
    mut v_opt_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2598_: *mut LeanObject = core::ptr::null_mut();
    v_res_2598_ =
        l_Lean_Option_get___at___00Lean_Meta_mkDiagSummary_spec__0(v_opts_2596_, v_opt_2597_);
    lean_dec_ref(v_opt_2597_);
    lean_dec_ref(v_opts_2596_);
    return v_res_2598_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__5(
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2606_: u8 = 0;
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2599_) == 0 {
                    v___x_2601_ = l_List_reverse___redArg(v_a_2600_);
                    return v___x_2601_;
                } else {
                    v_head_2602_ = lean_ctor_get(v_a_2599_, 0);
                    v_tail_2603_ = lean_ctor_get(v_a_2599_, 1);
                    v_isSharedCheck_2612_ = (!lean_is_exclusive(v_a_2599_)) as u8;
                    if v_isSharedCheck_2612_ == 0 {
                        v___x_2605_ = v_a_2599_;
                        v_isShared_2606_ = v_isSharedCheck_2612_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2603_);
                        lean_inc(v_head_2602_);
                        lean_dec(v_a_2599_);
                        v___x_2605_ = lean_box(0);
                        v_isShared_2606_ = v_isSharedCheck_2612_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2607_ = l_Lean_mkLevelParam(v_head_2602_);
                if v_isShared_2606_ == 0 {
                    lean_ctor_set(v___x_2605_, 1, v_a_2600_);
                    lean_ctor_set(v___x_2605_, 0, v___x_2607_);
                    v___x_2609_ = v___x_2605_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2607_);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_a_2600_);
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
-> *mut LeanObject {
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2613_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2613_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    v___x_2614_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__0);
    v___x_2615_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2615_, 0, v___x_2614_);
    return v___x_2615_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    v___x_2616_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1);
    v___x_2617_ = lean_unsigned_to_nat(0);
    v___x_2618_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2618_, 0, v___x_2617_);
    lean_ctor_set(v___x_2618_, 1, v___x_2617_);
    lean_ctor_set(v___x_2618_, 2, v___x_2617_);
    lean_ctor_set(v___x_2618_, 3, v___x_2617_);
    lean_ctor_set(v___x_2618_, 4, v___x_2616_);
    lean_ctor_set(v___x_2618_, 5, v___x_2616_);
    lean_ctor_set(v___x_2618_, 6, v___x_2616_);
    lean_ctor_set(v___x_2618_, 7, v___x_2616_);
    lean_ctor_set(v___x_2618_, 8, v___x_2616_);
    lean_ctor_set(v___x_2618_, 9, v___x_2616_);
    return v___x_2618_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    v___x_2619_ = lean_unsigned_to_nat(32);
    v___x_2620_ = lean_mk_empty_array_with_capacity(v___x_2619_);
    v___x_2621_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2621_, 0, v___x_2620_);
    return v___x_2621_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2622_: usize = 0;
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    v___x_2622_ = 5usize;
    v___x_2623_ = lean_unsigned_to_nat(0);
    v___x_2624_ = lean_unsigned_to_nat(32);
    v___x_2625_ = lean_mk_empty_array_with_capacity(v___x_2624_);
    v___x_2626_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__3);
    v___x_2627_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2627_, 0, v___x_2626_);
    lean_ctor_set(v___x_2627_, 1, v___x_2625_);
    lean_ctor_set(v___x_2627_, 2, v___x_2623_);
    lean_ctor_set(v___x_2627_, 3, v___x_2623_);
    lean_ctor_set_usize(v___x_2627_, 4, v___x_2622_);
    return v___x_2627_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    v___x_2628_ = lean_box(1);
    v___x_2629_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__4);
    v___x_2630_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__1);
    v___x_2631_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2631_, 0, v___x_2630_);
    lean_ctor_set(v___x_2631_, 1, v___x_2629_);
    lean_ctor_set(v___x_2631_, 2, v___x_2628_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    v___x_2633_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__6;
    v___x_2634_ = l_Lean_stringToMessageData(v___x_2633_);
    return v___x_2634_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__8;
    v___x_2637_ = l_Lean_stringToMessageData(v___x_2636_);
    return v___x_2637_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__10;
    v___x_2640_ = l_Lean_stringToMessageData(v___x_2639_);
    return v___x_2640_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__12;
    v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
    return v___x_2643_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__14;
    v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    v___x_2648_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__16;
    v___x_2649_ = l_Lean_stringToMessageData(v___x_2648_);
    return v___x_2649_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__18;
    v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
    return v___x_2652_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(
    mut v_msg_2653_: *mut LeanObject,
    mut v_declHint_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: u8 = 0;
    let mut v_isExporting_2660_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2657_ = lean_st_ref_get(v___y_2655_);
                v_env_2658_ = lean_ctor_get(v___x_2657_, 0);
                lean_inc_ref(v_env_2658_);
                lean_dec(v___x_2657_);
                v___x_2659_ = l_Lean_Name_isAnonymous(v_declHint_2654_);
                if v___x_2659_ == 0 {
                    v_isExporting_2660_ = lean_ctor_get_uint8(
                        v_env_2658_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2660_ == 0 {
                        lean_dec_ref(v_env_2658_);
                        lean_dec(v_declHint_2654_);
                        v___x_2661_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2661_, 0, v_msg_2653_);
                        return v___x_2661_;
                    } else {
                        lean_inc_ref(v_env_2658_);
                        v___x_2662_ = l_Lean_Environment_setExporting(v_env_2658_, v___x_2659_);
                        lean_inc(v_declHint_2654_);
                        lean_inc_ref(v___x_2662_);
                        v___x_2663_ = l_Lean_Environment_contains(
                            v___x_2662_,
                            v_declHint_2654_,
                            v_isExporting_2660_,
                        );
                        if v___x_2663_ == 0 {
                            lean_dec_ref(v___x_2662_);
                            lean_dec_ref(v_env_2658_);
                            lean_dec(v_declHint_2654_);
                            v___x_2664_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2664_, 0, v_msg_2653_);
                            return v___x_2664_;
                        } else {
                            v___x_2665_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__2);
                            v___x_2666_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__5);
                            v___x_2667_ = l_Lean_Options_empty;
                            v___x_2668_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2668_, 0, v___x_2662_);
                            lean_ctor_set(v___x_2668_, 1, v___x_2665_);
                            lean_ctor_set(v___x_2668_, 2, v___x_2666_);
                            lean_ctor_set(v___x_2668_, 3, v___x_2667_);
                            lean_inc(v_declHint_2654_);
                            v___x_2669_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2654_, v___x_2659_);
                            v_c_2670_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2670_, 0, v___x_2668_);
                            lean_ctor_set(v_c_2670_, 1, v___x_2669_);
                            v___x_2671_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2658_,
                                v_declHint_2654_,
                            );
                            if lean_obj_tag(v___x_2671_) == 0 {
                                lean_dec_ref(v_env_2658_);
                                lean_dec(v_declHint_2654_);
                                v___x_2672_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7);
                                v___x_2673_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2673_, 0, v___x_2672_);
                                lean_ctor_set(v___x_2673_, 1, v_c_2670_);
                                v___x_2674_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__9);
                                v___x_2675_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2675_, 0, v___x_2673_);
                                lean_ctor_set(v___x_2675_, 1, v___x_2674_);
                                v___x_2676_ = l_Lean_MessageData_note(v___x_2675_);
                                v___x_2677_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2677_, 0, v_msg_2653_);
                                lean_ctor_set(v___x_2677_, 1, v___x_2676_);
                                v___x_2678_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2678_, 0, v___x_2677_);
                                return v___x_2678_;
                            } else {
                                v_val_2679_ = lean_ctor_get(v___x_2671_, 0);
                                v_isSharedCheck_2714_ = (!lean_is_exclusive(v___x_2671_)) as u8;
                                if v_isSharedCheck_2714_ == 0 {
                                    v___x_2681_ = v___x_2671_;
                                    v_isShared_2682_ = v_isSharedCheck_2714_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2679_);
                                    lean_dec(v___x_2671_);
                                    v___x_2681_ = lean_box(0);
                                    v_isShared_2682_ = v_isSharedCheck_2714_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2658_);
                    lean_dec(v_declHint_2654_);
                    v___x_2715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2715_, 0, v_msg_2653_);
                    return v___x_2715_;
                }
            }
            1 => {
                v___x_2683_ = lean_box(0);
                v___x_2684_ = l_Lean_Environment_header(v_env_2658_);
                lean_dec_ref(v_env_2658_);
                v___x_2685_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2684_);
                v_mod_2686_ = lean_array_get(v___x_2683_, v___x_2685_, v_val_2679_);
                lean_dec(v_val_2679_);
                lean_dec_ref(v___x_2685_);
                v___x_2687_ = l_Lean_isPrivateName(v_declHint_2654_);
                lean_dec(v_declHint_2654_);
                if v___x_2687_ == 0 {
                    v___x_2688_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__11);
                    v___x_2689_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2689_, 0, v___x_2688_);
                    lean_ctor_set(v___x_2689_, 1, v_c_2670_);
                    v___x_2690_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__13);
                    v___x_2691_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2691_, 0, v___x_2689_);
                    lean_ctor_set(v___x_2691_, 1, v___x_2690_);
                    v___x_2692_ = l_Lean_MessageData_ofName(v_mod_2686_);
                    v___x_2693_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2693_, 0, v___x_2691_);
                    lean_ctor_set(v___x_2693_, 1, v___x_2692_);
                    v___x_2694_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__15);
                    v___x_2695_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2695_, 0, v___x_2693_);
                    lean_ctor_set(v___x_2695_, 1, v___x_2694_);
                    v___x_2696_ = l_Lean_MessageData_note(v___x_2695_);
                    v___x_2697_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2697_, 0, v_msg_2653_);
                    lean_ctor_set(v___x_2697_, 1, v___x_2696_);
                    if v_isShared_2682_ == 0 {
                        lean_ctor_set_tag(v___x_2681_, 0);
                        lean_ctor_set(v___x_2681_, 0, v___x_2697_);
                        v___x_2699_ = v___x_2681_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
                        v___x_2699_ = v_reuseFailAlloc_2700_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2701_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__7);
                    v___x_2702_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2702_, 0, v___x_2701_);
                    lean_ctor_set(v___x_2702_, 1, v_c_2670_);
                    v___x_2703_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__17);
                    v___x_2704_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2704_, 0, v___x_2702_);
                    lean_ctor_set(v___x_2704_, 1, v___x_2703_);
                    v___x_2705_ = l_Lean_MessageData_ofName(v_mod_2686_);
                    v___x_2706_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2706_, 0, v___x_2704_);
                    lean_ctor_set(v___x_2706_, 1, v___x_2705_);
                    v___x_2707_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg___closed__19);
                    v___x_2708_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2708_, 0, v___x_2706_);
                    lean_ctor_set(v___x_2708_, 1, v___x_2707_);
                    v___x_2709_ = l_Lean_MessageData_note(v___x_2708_);
                    v___x_2710_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2710_, 0, v_msg_2653_);
                    lean_ctor_set(v___x_2710_, 1, v___x_2709_);
                    if v_isShared_2682_ == 0 {
                        lean_ctor_set_tag(v___x_2681_, 0);
                        lean_ctor_set(v___x_2681_, 0, v___x_2710_);
                        v___x_2712_ = v___x_2681_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
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
    mut v_msg_2716_: *mut LeanObject,
    mut v_declHint_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2720_: *mut LeanObject = core::ptr::null_mut();
    v_res_2720_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(v_msg_2716_, v_declHint_2717_, v___y_2718_);
    lean_dec(v___y_2718_);
    return v_res_2720_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15(
    mut v_msg_2721_: *mut LeanObject,
    mut v_declHint_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
    mut v___y_2724_: *mut LeanObject,
    mut v___y_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2728_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(v_msg_2721_, v_declHint_2722_, v___y_2726_);
                v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
                v_isSharedCheck_2738_ = (!lean_is_exclusive(v___x_2728_)) as u8;
                if v_isSharedCheck_2738_ == 0 {
                    v___x_2731_ = v___x_2728_;
                    v_isShared_2732_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2729_);
                    lean_dec(v___x_2728_);
                    v___x_2731_ = lean_box(0);
                    v_isShared_2732_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2733_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2734_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2734_, 0, v___x_2733_);
                lean_ctor_set(v___x_2734_, 1, v_a_2729_);
                if v_isShared_2732_ == 0 {
                    lean_ctor_set(v___x_2731_, 0, v___x_2734_);
                    v___x_2736_ = v___x_2731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
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
    mut v_msg_2739_: *mut LeanObject,
    mut v_declHint_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
    mut v___y_2745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2746_: *mut LeanObject = core::ptr::null_mut();
    v_res_2746_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15(v_msg_2739_, v_declHint_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
    lean_dec(v___y_2744_);
    lean_dec_ref(v___y_2743_);
    lean_dec(v___y_2742_);
    lean_dec_ref(v___y_2741_);
    return v_res_2746_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(
    mut v_msgData_2747_: *mut LeanObject,
    mut v___y_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    v___x_2753_ = lean_st_ref_get(v___y_2751_);
    v_env_2754_ = lean_ctor_get(v___x_2753_, 0);
    lean_inc_ref(v_env_2754_);
    lean_dec(v___x_2753_);
    v___x_2755_ = lean_st_ref_get(v___y_2749_);
    v_mctx_2756_ = lean_ctor_get(v___x_2755_, 0);
    lean_inc_ref(v_mctx_2756_);
    lean_dec(v___x_2755_);
    v_lctx_2757_ = lean_ctor_get(v___y_2748_, 2);
    v_options_2758_ = lean_ctor_get(v___y_2750_, 2);
    lean_inc_ref(v_options_2758_);
    lean_inc_ref(v_lctx_2757_);
    v___x_2759_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2759_, 0, v_env_2754_);
    lean_ctor_set(v___x_2759_, 1, v_mctx_2756_);
    lean_ctor_set(v___x_2759_, 2, v_lctx_2757_);
    lean_ctor_set(v___x_2759_, 3, v_options_2758_);
    v___x_2760_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2760_, 0, v___x_2759_);
    lean_ctor_set(v___x_2760_, 1, v_msgData_2747_);
    v___x_2761_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2761_, 0, v___x_2760_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19___boxed(
    mut v_msgData_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
    mut v___y_2765_: *mut LeanObject,
    mut v___y_2766_: *mut LeanObject,
    mut v___y_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2768_: *mut LeanObject = core::ptr::null_mut();
    v_res_2768_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(v_msgData_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
    lean_dec(v___y_2766_);
    lean_dec_ref(v___y_2765_);
    lean_dec(v___y_2764_);
    lean_dec_ref(v___y_2763_);
    return v_res_2768_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(
    mut v_msg_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
    mut v___y_2772_: *mut LeanObject,
    mut v___y_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2775_ = lean_ctor_get(v___y_2772_, 5);
                v___x_2776_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
                v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
                v_isSharedCheck_2785_ = (!lean_is_exclusive(v___x_2776_)) as u8;
                if v_isSharedCheck_2785_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    v_isShared_2780_ = v_isSharedCheck_2785_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2777_);
                    lean_dec(v___x_2776_);
                    v___x_2779_ = lean_box(0);
                    v_isShared_2780_ = v_isSharedCheck_2785_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2775_);
                v___x_2781_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2781_, 0, v_ref_2775_);
                lean_ctor_set(v___x_2781_, 1, v_a_2777_);
                if v_isShared_2780_ == 0 {
                    lean_ctor_set_tag(v___x_2779_, 1);
                    lean_ctor_set(v___x_2779_, 0, v___x_2781_);
                    v___x_2783_ = v___x_2779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
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
    mut v_msg_2786_: *mut LeanObject,
    mut v___y_2787_: *mut LeanObject,
    mut v___y_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
    mut v___y_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2792_: *mut LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(v_msg_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
    lean_dec(v___y_2790_);
    lean_dec_ref(v___y_2789_);
    lean_dec(v___y_2788_);
    lean_dec_ref(v___y_2787_);
    return v_res_2792_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(
    mut v_ref_2793_: *mut LeanObject,
    mut v_msg_2794_: *mut LeanObject,
    mut v___y_2795_: *mut LeanObject,
    mut v___y_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2812_: u8 = 0;
    let mut v_cancelTk_x3f_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2814_: u8 = 0;
    let mut v_inheritedTraceOptions_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2800_ = lean_ctor_get(v___y_2797_, 0);
    v_fileMap_2801_ = lean_ctor_get(v___y_2797_, 1);
    v_options_2802_ = lean_ctor_get(v___y_2797_, 2);
    v_currRecDepth_2803_ = lean_ctor_get(v___y_2797_, 3);
    v_maxRecDepth_2804_ = lean_ctor_get(v___y_2797_, 4);
    v_ref_2805_ = lean_ctor_get(v___y_2797_, 5);
    v_currNamespace_2806_ = lean_ctor_get(v___y_2797_, 6);
    v_openDecls_2807_ = lean_ctor_get(v___y_2797_, 7);
    v_initHeartbeats_2808_ = lean_ctor_get(v___y_2797_, 8);
    v_maxHeartbeats_2809_ = lean_ctor_get(v___y_2797_, 9);
    v_quotContext_2810_ = lean_ctor_get(v___y_2797_, 10);
    v_currMacroScope_2811_ = lean_ctor_get(v___y_2797_, 11);
    v_diag_2812_ = lean_ctor_get_uint8(
        v___y_2797_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2813_ = lean_ctor_get(v___y_2797_, 12);
    v_suppressElabErrors_2814_ = lean_ctor_get_uint8(
        v___y_2797_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2815_ = lean_ctor_get(v___y_2797_, 13);
    v_ref_2816_ = l_Lean_replaceRef(v_ref_2793_, v_ref_2805_);
    lean_inc_ref(v_inheritedTraceOptions_2815_);
    lean_inc(v_cancelTk_x3f_2813_);
    lean_inc(v_currMacroScope_2811_);
    lean_inc(v_quotContext_2810_);
    lean_inc(v_maxHeartbeats_2809_);
    lean_inc(v_initHeartbeats_2808_);
    lean_inc(v_openDecls_2807_);
    lean_inc(v_currNamespace_2806_);
    lean_inc(v_maxRecDepth_2804_);
    lean_inc(v_currRecDepth_2803_);
    lean_inc_ref(v_options_2802_);
    lean_inc_ref(v_fileMap_2801_);
    lean_inc_ref(v_fileName_2800_);
    v___x_2817_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2817_, 0, v_fileName_2800_);
    lean_ctor_set(v___x_2817_, 1, v_fileMap_2801_);
    lean_ctor_set(v___x_2817_, 2, v_options_2802_);
    lean_ctor_set(v___x_2817_, 3, v_currRecDepth_2803_);
    lean_ctor_set(v___x_2817_, 4, v_maxRecDepth_2804_);
    lean_ctor_set(v___x_2817_, 5, v_ref_2816_);
    lean_ctor_set(v___x_2817_, 6, v_currNamespace_2806_);
    lean_ctor_set(v___x_2817_, 7, v_openDecls_2807_);
    lean_ctor_set(v___x_2817_, 8, v_initHeartbeats_2808_);
    lean_ctor_set(v___x_2817_, 9, v_maxHeartbeats_2809_);
    lean_ctor_set(v___x_2817_, 10, v_quotContext_2810_);
    lean_ctor_set(v___x_2817_, 11, v_currMacroScope_2811_);
    lean_ctor_set(v___x_2817_, 12, v_cancelTk_x3f_2813_);
    lean_ctor_set(v___x_2817_, 13, v_inheritedTraceOptions_2815_);
    lean_ctor_set_uint8(
        v___x_2817_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2812_,
    );
    lean_ctor_set_uint8(
        v___x_2817_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2814_,
    );
    v___x_2818_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(v_msg_2794_, v___y_2795_, v___y_2796_, v___x_2817_, v___y_2798_);
    lean_dec_ref_known(v___x_2817_, 14);
    return v___x_2818_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg___boxed(
    mut v_ref_2819_: *mut LeanObject,
    mut v_msg_2820_: *mut LeanObject,
    mut v___y_2821_: *mut LeanObject,
    mut v___y_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
    mut v___y_2824_: *mut LeanObject,
    mut v___y_2825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2826_: *mut LeanObject = core::ptr::null_mut();
    v_res_2826_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(v_ref_2819_, v_msg_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
    lean_dec(v___y_2824_);
    lean_dec_ref(v___y_2823_);
    lean_dec(v___y_2822_);
    lean_dec_ref(v___y_2821_);
    lean_dec(v_ref_2819_);
    return v_res_2826_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(
    mut v_ref_2827_: *mut LeanObject,
    mut v_msg_2828_: *mut LeanObject,
    mut v_declHint_2829_: *mut LeanObject,
    mut v___y_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15(v_msg_2828_, v_declHint_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
    v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
    lean_inc(v_a_2836_);
    lean_dec_ref(v___x_2835_);
    v___x_2837_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(v_ref_2827_, v_a_2836_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
    return v___x_2837_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg___boxed(
    mut v_ref_2838_: *mut LeanObject,
    mut v_msg_2839_: *mut LeanObject,
    mut v_declHint_2840_: *mut LeanObject,
    mut v___y_2841_: *mut LeanObject,
    mut v___y_2842_: *mut LeanObject,
    mut v___y_2843_: *mut LeanObject,
    mut v___y_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2846_: *mut LeanObject = core::ptr::null_mut();
    v_res_2846_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(v_ref_2838_, v_msg_2839_, v_declHint_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
    lean_dec(v___y_2844_);
    lean_dec_ref(v___y_2843_);
    lean_dec(v___y_2842_);
    lean_dec_ref(v___y_2841_);
    lean_dec(v_ref_2838_);
    return v_res_2846_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    v___x_2848_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__0;
    v___x_2849_ = l_Lean_stringToMessageData(v___x_2848_);
    return v___x_2849_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    v___x_2851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__2;
    v___x_2852_ = l_Lean_stringToMessageData(v___x_2851_);
    return v___x_2852_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(
    mut v_ref_2853_: *mut LeanObject,
    mut v_constName_2854_: *mut LeanObject,
    mut v___y_2855_: *mut LeanObject,
    mut v___y_2856_: *mut LeanObject,
    mut v___y_2857_: *mut LeanObject,
    mut v___y_2858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    v___x_2860_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__1);
    v___x_2861_ = 0;
    lean_inc(v_constName_2854_);
    v___x_2862_ = l_Lean_MessageData_ofConstName(v_constName_2854_, v___x_2861_);
    v___x_2863_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2863_, 0, v___x_2860_);
    lean_ctor_set(v___x_2863_, 1, v___x_2862_);
    v___x_2864_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___closed__3);
    v___x_2865_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2865_, 0, v___x_2863_);
    lean_ctor_set(v___x_2865_, 1, v___x_2864_);
    v___x_2866_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(v_ref_2853_, v___x_2865_, v_constName_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
    return v___x_2866_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg___boxed(
    mut v_ref_2867_: *mut LeanObject,
    mut v_constName_2868_: *mut LeanObject,
    mut v___y_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2874_: *mut LeanObject = core::ptr::null_mut();
    v_res_2874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(v_ref_2867_, v_constName_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
    lean_dec(v___y_2872_);
    lean_dec_ref(v___y_2871_);
    lean_dec(v___y_2870_);
    lean_dec_ref(v___y_2869_);
    lean_dec(v_ref_2867_);
    return v_res_2874_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(
    mut v_constName_2875_: *mut LeanObject,
    mut v___y_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
    mut v___y_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2881_ = lean_ctor_get(v___y_2878_, 5);
    v___x_2882_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(v_ref_2881_, v_constName_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
    return v___x_2882_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_constName_2883_: *mut LeanObject,
    mut v___y_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
    mut v___y_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
    mut v___y_2888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2889_: *mut LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(v_constName_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    lean_dec(v___y_2887_);
    lean_dec_ref(v___y_2886_);
    lean_dec(v___y_2885_);
    lean_dec_ref(v___y_2884_);
    return v_res_2889_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4(
    mut v_constName_2890_: *mut LeanObject,
    mut v___y_2891_: *mut LeanObject,
    mut v___y_2892_: *mut LeanObject,
    mut v___y_2893_: *mut LeanObject,
    mut v___y_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2896_ = lean_st_ref_get(v___y_2894_);
                v_env_2897_ = lean_ctor_get(v___x_2896_, 0);
                lean_inc_ref(v_env_2897_);
                lean_dec(v___x_2896_);
                v___x_2898_ = 0;
                lean_inc(v_constName_2890_);
                v___x_2899_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2897_,
                    v_constName_2890_,
                    v___x_2898_,
                );
                if lean_obj_tag(v___x_2899_) == 0 {
                    v___x_2900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(v_constName_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
                    return v___x_2900_;
                } else {
                    lean_dec(v_constName_2890_);
                    v_val_2901_ = lean_ctor_get(v___x_2899_, 0);
                    v_isSharedCheck_2908_ = (!lean_is_exclusive(v___x_2899_)) as u8;
                    if v_isSharedCheck_2908_ == 0 {
                        v___x_2903_ = v___x_2899_;
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2901_);
                        lean_dec(v___x_2899_);
                        v___x_2903_ = lean_box(0);
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2904_ == 0 {
                    lean_ctor_set_tag(v___x_2903_, 0);
                    v___x_2906_ = v___x_2903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_val_2901_);
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
    mut v_constName_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2915_: *mut LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4(v_constName_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
    lean_dec(v___y_2913_);
    lean_dec_ref(v___y_2912_);
    lean_dec(v___y_2911_);
    lean_dec_ref(v___y_2910_);
    return v_res_2915_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2(
    mut v_constName_2916_: *mut LeanObject,
    mut v___y_2917_: *mut LeanObject,
    mut v___y_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v_levelParams_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_a_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_2916_);
                v___x_2922_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4(v_constName_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
                if lean_obj_tag(v___x_2922_) == 0 {
                    v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2934_ = (!lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2934_ == 0 {
                        v___x_2925_ = v___x_2922_;
                        v_isShared_2926_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2923_);
                        lean_dec(v___x_2922_);
                        v___x_2925_ = lean_box(0);
                        v_isShared_2926_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_2916_);
                    v_a_2935_ = lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2942_ = (!lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2942_ == 0 {
                        v___x_2937_ = v___x_2922_;
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2935_);
                        lean_dec(v___x_2922_);
                        v___x_2937_ = lean_box(0);
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_2927_ = lean_ctor_get(v_a_2923_, 1);
                lean_inc(v_levelParams_2927_);
                lean_dec(v_a_2923_);
                v___x_2928_ = lean_box(0);
                v___x_2929_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__5(v_levelParams_2927_, v___x_2928_);
                v___x_2930_ = l_Lean_mkConst(v_constName_2916_, v___x_2929_);
                if v_isShared_2926_ == 0 {
                    lean_ctor_set(v___x_2925_, 0, v___x_2930_);
                    v___x_2932_ = v___x_2925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
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
                    v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
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
    mut v_constName_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2949_: *mut LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2(
        v_constName_2943_,
        v___y_2944_,
        v___y_2945_,
        v___y_2946_,
        v___y_2947_,
    );
    lean_dec(v___y_2947_);
    lean_dec_ref(v___y_2946_);
    lean_dec(v___y_2945_);
    lean_dec_ref(v___y_2944_);
    return v_res_2949_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0()
-> f64 {
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: f64 = 0.0;
    v___x_2950_ = lean_unsigned_to_nat(0);
    v___x_2951_ = lean_float_of_nat(v___x_2950_);
    return v___x_2951_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__2;
    v___x_2955_ = l_Lean_stringToMessageData(v___x_2954_);
    return v___x_2955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3(
    mut v_cls_2956_: *mut LeanObject,
    mut v_as_2957_: *mut LeanObject,
    mut v_sz_2958_: usize,
    mut v_i_2959_: usize,
    mut v_b_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2973_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: f64 = 0.0;
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: usize = 0;
    let mut v_reuseFailAlloc_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2966_ = lean_usize_dec_lt(v_i_2959_, v_sz_2958_);
                if v___x_2966_ == 0 {
                    lean_dec(v_cls_2956_);
                    v___x_2967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2967_, 0, v_b_2960_);
                    return v___x_2967_;
                } else {
                    v_a_2968_ = lean_array_uget(v_as_2957_, v_i_2959_);
                    v_fst_2969_ = lean_ctor_get(v_a_2968_, 0);
                    v_snd_2970_ = lean_ctor_get(v_a_2968_, 1);
                    v_isSharedCheck_3003_ = (!lean_is_exclusive(v_a_2968_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2972_ = v_a_2968_;
                        v_isShared_2973_ = v_isSharedCheck_3003_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2970_);
                        lean_inc(v_fst_2969_);
                        lean_dec(v_a_2968_);
                        v___x_2972_ = lean_box(0);
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
                if lean_obj_tag(v___x_2974_) == 0 {
                    v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
                    lean_inc(v_a_2975_);
                    lean_dec_ref_known(v___x_2974_, 1);
                    v___x_2976_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__0;
                    v___x_2977_ = lean_box(0);
                    v___x_2978_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0);
                    v___x_2979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
                    lean_inc(v_cls_2956_);
                    v___x_2980_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v___x_2980_, 0, v_cls_2956_);
                    lean_ctor_set(v___x_2980_, 1, v___x_2977_);
                    lean_ctor_set(v___x_2980_, 2, v___x_2979_);
                    lean_ctor_set_float(
                        v___x_2980_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_2978_,
                    );
                    lean_ctor_set_float(
                        v___x_2980_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_2978_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2980_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v___x_2966_,
                    );
                    v___x_2981_ = l_Lean_MessageData_ofConst(v_a_2975_);
                    v___x_2982_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__3);
                    if v_isShared_2973_ == 0 {
                        lean_ctor_set_tag(v___x_2972_, 7);
                        lean_ctor_set(v___x_2972_, 1, v___x_2982_);
                        lean_ctor_set(v___x_2972_, 0, v___x_2981_);
                        v___x_2984_ = v___x_2972_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2994_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2981_);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2982_);
                        v___x_2984_ = v_reuseFailAlloc_2994_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2972_);
                    lean_dec(v_snd_2970_);
                    lean_dec_ref(v_b_2960_);
                    lean_dec(v_cls_2956_);
                    v_a_2995_ = lean_ctor_get(v___x_2974_, 0);
                    v_isSharedCheck_3002_ = (!lean_is_exclusive(v___x_2974_)) as u8;
                    if v_isSharedCheck_3002_ == 0 {
                        v___x_2997_ = v___x_2974_;
                        v_isShared_2998_ = v_isSharedCheck_3002_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2995_);
                        lean_dec(v___x_2974_);
                        v___x_2997_ = lean_box(0);
                        v_isShared_2998_ = v_isSharedCheck_3002_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2985_ = l_Nat_reprFast(v_snd_2970_);
                v___x_2986_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2986_, 0, v___x_2985_);
                v___x_2987_ = l_Lean_MessageData_ofFormat(v___x_2986_);
                v___x_2988_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2988_, 0, v___x_2984_);
                lean_ctor_set(v___x_2988_, 1, v___x_2987_);
                v___x_2989_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2989_, 0, v___x_2980_);
                lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                lean_ctor_set(v___x_2989_, 2, v___x_2976_);
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
                    v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
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
    mut v_cls_3004_: *mut LeanObject,
    mut v_as_3005_: *mut LeanObject,
    mut v_sz_3006_: *mut LeanObject,
    mut v_i_3007_: *mut LeanObject,
    mut v_b_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3014_: usize = 0;
    let mut v_i_boxed_3015_: usize = 0;
    let mut v_res_3016_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3006_);
    lean_dec(v_sz_3006_);
    v_i_boxed_3015_ = lean_unbox_usize(v_i_3007_);
    lean_dec(v_i_3007_);
    v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3(v_cls_3004_, v_as_3005_, v_sz_boxed_3014_, v_i_boxed_3015_, v_b_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
    lean_dec(v___y_3012_);
    lean_dec_ref(v___y_3011_);
    lean_dec(v___y_3010_);
    lean_dec_ref(v___y_3009_);
    lean_dec_ref(v_as_3005_);
    return v_res_3016_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(
    mut v_lt_3017_: *mut LeanObject,
    mut v_hi_3018_: *mut LeanObject,
    mut v_pivot_3019_: *mut LeanObject,
    mut v_as_3020_: *mut LeanObject,
    mut v_i_3021_: *mut LeanObject,
    mut v_k_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3033_ = lean_nat_dec_lt(v_k_3022_, v_hi_3018_);
                if v___x_3033_ == 0 {
                    lean_dec(v_k_3022_);
                    lean_dec_ref(v_pivot_3019_);
                    lean_dec_ref(v_lt_3017_);
                    v___x_3034_ = lean_array_fswap(v_as_3020_, v_i_3021_, v_hi_3018_);
                    v___x_3035_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3035_, 0, v_i_3021_);
                    lean_ctor_set(v___x_3035_, 1, v___x_3034_);
                    return v___x_3035_;
                } else {
                    v___x_3036_ = lean_array_fget_borrowed(v_as_3020_, v_k_3022_);
                    v_fst_3037_ = lean_ctor_get(v___x_3036_, 0);
                    v_snd_3038_ = lean_ctor_get(v___x_3036_, 1);
                    v_fst_3039_ = lean_ctor_get(v_pivot_3019_, 0);
                    v_snd_3040_ = lean_ctor_get(v_pivot_3019_, 1);
                    v___x_3041_ = lean_nat_dec_eq(v_snd_3038_, v_snd_3040_);
                    if v___x_3041_ == 0 {
                        v___x_3042_ = lean_nat_dec_lt(v_snd_3040_, v_snd_3038_);
                        v___y_3024_ = v___x_3042_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_lt_3017_);
                        lean_inc(v_fst_3039_);
                        lean_inc(v_fst_3037_);
                        v___x_3043_ = lean_apply_2(v_lt_3017_, v_fst_3037_, v_fst_3039_);
                        v___x_3044_ = (lean_unbox(v___x_3043_) as u8);
                        v___y_3024_ = v___x_3044_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3024_ == 0 {
                    v___x_3025_ = lean_unsigned_to_nat(1);
                    v___x_3026_ = lean_nat_add(v_k_3022_, v___x_3025_);
                    lean_dec(v_k_3022_);
                    v_k_3022_ = v___x_3026_;
                    state = 0;
                    continue;
                } else {
                    v___x_3028_ = lean_array_fswap(v_as_3020_, v_i_3021_, v_k_3022_);
                    v___x_3029_ = lean_unsigned_to_nat(1);
                    v___x_3030_ = lean_nat_add(v_i_3021_, v___x_3029_);
                    lean_dec(v_i_3021_);
                    v___x_3031_ = lean_nat_add(v_k_3022_, v___x_3029_);
                    lean_dec(v_k_3022_);
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
    mut v_lt_3045_: *mut LeanObject,
    mut v_hi_3046_: *mut LeanObject,
    mut v_pivot_3047_: *mut LeanObject,
    mut v_as_3048_: *mut LeanObject,
    mut v_i_3049_: *mut LeanObject,
    mut v_k_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3051_: *mut LeanObject = core::ptr::null_mut();
    v_res_3051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_3045_, v_hi_3046_, v_pivot_3047_, v_as_3048_, v_i_3049_, v_k_3050_);
    lean_dec(v_hi_3046_);
    return v_res_3051_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(
    mut v_lt_3052_: *mut LeanObject,
    mut v_x_3053_: *mut LeanObject,
    mut v_x_3054_: *mut LeanObject,
) -> u8 {
    let mut v_fst_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    v_fst_3055_ = lean_ctor_get(v_x_3053_, 0);
    lean_inc(v_fst_3055_);
    v_snd_3056_ = lean_ctor_get(v_x_3053_, 1);
    lean_inc(v_snd_3056_);
    lean_dec_ref(v_x_3053_);
    v_fst_3057_ = lean_ctor_get(v_x_3054_, 0);
    lean_inc(v_fst_3057_);
    v_snd_3058_ = lean_ctor_get(v_x_3054_, 1);
    lean_inc(v_snd_3058_);
    lean_dec_ref(v_x_3054_);
    v___x_3059_ = lean_nat_dec_eq(v_snd_3056_, v_snd_3058_);
    if v___x_3059_ == 0 {
        let mut v___x_3060_: u8 = 0;
        lean_dec(v_fst_3057_);
        lean_dec(v_fst_3055_);
        lean_dec_ref(v_lt_3052_);
        v___x_3060_ = lean_nat_dec_lt(v_snd_3058_, v_snd_3056_);
        lean_dec(v_snd_3056_);
        lean_dec(v_snd_3058_);
        return v___x_3060_;
    } else {
        let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3062_: u8 = 0;
        lean_dec(v_snd_3058_);
        lean_dec(v_snd_3056_);
        v___x_3061_ = lean_apply_2(v_lt_3052_, v_fst_3055_, v_fst_3057_);
        v___x_3062_ = (lean_unbox(v___x_3061_) as u8);
        return v___x_3062_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0___boxed(
    mut v_lt_3063_: *mut LeanObject,
    mut v_x_3064_: *mut LeanObject,
    mut v_x_3065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3066_: u8 = 0;
    let mut v_r_3067_: *mut LeanObject = core::ptr::null_mut();
    v_res_3066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_3063_, v_x_3064_, v_x_3065_);
    v_r_3067_ = lean_box((v_res_3066_) as usize);
    return v_r_3067_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(
    mut v_lt_3068_: *mut LeanObject,
    mut v_n_3069_: *mut LeanObject,
    mut v_as_3070_: *mut LeanObject,
    mut v_lo_3071_: *mut LeanObject,
    mut v_hi_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: u8 = 0;
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3084_ = lean_nat_dec_lt(v_lo_3071_, v_hi_3072_);
                if v___x_3084_ == 0 {
                    lean_dec(v_lo_3071_);
                    lean_dec_ref(v_lt_3068_);
                    return v_as_3070_;
                } else {
                    v___x_3085_ = lean_nat_add(v_lo_3071_, v_hi_3072_);
                    v___x_3086_ = lean_unsigned_to_nat(1);
                    v_mid_3087_ = lean_nat_shiftr(v___x_3085_, v___x_3086_);
                    lean_dec(v___x_3085_);
                    v___x_3100_ = lean_array_fget_borrowed(v_as_3070_, v_mid_3087_);
                    v___x_3101_ = lean_array_fget_borrowed(v_as_3070_, v_lo_3071_);
                    lean_inc(v___x_3101_);
                    lean_inc(v___x_3100_);
                    lean_inc_ref(v_lt_3068_);
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
                lean_inc_n(v_lo_3071_, 2);
                lean_inc_ref(v_lt_3068_);
                v___x_3076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_3068_, v_hi_3072_, v_pivot_3075_, v___y_3074_, v_lo_3071_, v_lo_3071_);
                v_fst_3077_ = lean_ctor_get(v___x_3076_, 0);
                lean_inc(v_fst_3077_);
                v_snd_3078_ = lean_ctor_get(v___x_3076_, 1);
                lean_inc(v_snd_3078_);
                lean_dec_ref(v___x_3076_);
                v___x_3079_ = lean_nat_dec_le(v_hi_3072_, v_fst_3077_);
                if v___x_3079_ == 0 {
                    lean_inc_ref(v_lt_3068_);
                    v___x_3080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3068_, v_n_3069_, v_snd_3078_, v_lo_3071_, v_fst_3077_);
                    v___x_3081_ = lean_unsigned_to_nat(1);
                    v___x_3082_ = lean_nat_add(v_fst_3077_, v___x_3081_);
                    lean_dec(v_fst_3077_);
                    v_as_3070_ = v___x_3080_;
                    v_lo_3071_ = v___x_3082_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_3077_);
                    lean_dec(v_lo_3071_);
                    lean_dec_ref(v_lt_3068_);
                    return v_snd_3078_;
                }
            }
            2 => {
                v___x_3090_ = lean_array_fget_borrowed(v___y_3089_, v_mid_3087_);
                v___x_3091_ = lean_array_fget_borrowed(v___y_3089_, v_hi_3072_);
                lean_inc(v___x_3091_);
                lean_inc(v___x_3090_);
                lean_inc_ref(v_lt_3068_);
                v___x_3092_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_3068_, v___x_3090_, v___x_3091_);
                if v___x_3092_ == 0 {
                    lean_dec(v_mid_3087_);
                    v___y_3074_ = v___y_3089_;
                    state = 1;
                    continue;
                } else {
                    v___x_3093_ = lean_array_fswap(v___y_3089_, v_mid_3087_, v_hi_3072_);
                    lean_dec(v_mid_3087_);
                    v___y_3074_ = v___x_3093_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3096_ = lean_array_fget_borrowed(v___y_3095_, v_hi_3072_);
                v___x_3097_ = lean_array_fget_borrowed(v___y_3095_, v_lo_3071_);
                lean_inc(v___x_3097_);
                lean_inc(v___x_3096_);
                lean_inc_ref(v_lt_3068_);
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
    mut v_lt_3104_: *mut LeanObject,
    mut v_n_3105_: *mut LeanObject,
    mut v_as_3106_: *mut LeanObject,
    mut v_lo_3107_: *mut LeanObject,
    mut v_hi_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3109_: *mut LeanObject = core::ptr::null_mut();
    v_res_3109_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3104_, v_n_3105_, v_as_3106_, v_lo_3107_, v_hi_3108_);
    lean_dec(v_hi_3108_);
    lean_dec(v_n_3105_);
    return v_res_3109_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg___lam__0(
    mut v_f_3110_: *mut LeanObject,
    mut v_s_3111_: *mut LeanObject,
    mut v_a_3112_: *mut LeanObject,
    mut v_b_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_a_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3131_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3114_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3114_, 0, v_a_3112_);
                lean_ctor_set(v___x_3114_, 1, v_b_3113_);
                v___x_3115_ = lean_apply_2(v_f_3110_, v___x_3114_, v_s_3111_);
                if lean_obj_tag(v___x_3115_) == 0 {
                    v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3123_ = (!lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3123_ == 0 {
                        v___x_3118_ = v___x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3123_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3116_);
                        lean_dec(v___x_3115_);
                        v___x_3118_ = lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3123_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3124_ = lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3131_ = (!lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3131_ == 0 {
                        v___x_3126_ = v___x_3115_;
                        v_isShared_3127_ = v_isSharedCheck_3131_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3124_);
                        lean_dec(v___x_3115_);
                        v___x_3126_ = lean_box(0);
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
                    v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
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
                    v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
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
    mut v_f_3132_: *mut LeanObject,
    mut v_keys_3133_: *mut LeanObject,
    mut v_vals_3134_: *mut LeanObject,
    mut v_i_3135_: *mut LeanObject,
    mut v_acc_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: u8 = 0;
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3137_ = lean_array_get_size(v_keys_3133_);
                v___x_3138_ = lean_nat_dec_lt(v_i_3135_, v___x_3137_);
                if v___x_3138_ == 0 {
                    lean_dec(v_i_3135_);
                    lean_dec_ref(v_f_3132_);
                    v___x_3139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3139_, 0, v_acc_3136_);
                    return v___x_3139_;
                } else {
                    v_k_3140_ = lean_array_fget_borrowed(v_keys_3133_, v_i_3135_);
                    v_v_3141_ = lean_array_fget_borrowed(v_vals_3134_, v_i_3135_);
                    lean_inc_ref(v_f_3132_);
                    lean_inc(v_v_3141_);
                    lean_inc(v_k_3140_);
                    v___x_3142_ = lean_apply_3(v_f_3132_, v_acc_3136_, v_k_3140_, v_v_3141_);
                    if lean_obj_tag(v___x_3142_) == 0 {
                        lean_dec(v_i_3135_);
                        lean_dec_ref(v_f_3132_);
                        return v___x_3142_;
                    } else {
                        v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
                        lean_inc(v_a_3143_);
                        lean_dec_ref_known(v___x_3142_, 1);
                        v___x_3144_ = lean_unsigned_to_nat(1);
                        v___x_3145_ = lean_nat_add(v_i_3135_, v___x_3144_);
                        lean_dec(v_i_3135_);
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
    mut v_f_3147_: *mut LeanObject,
    mut v_keys_3148_: *mut LeanObject,
    mut v_vals_3149_: *mut LeanObject,
    mut v_i_3150_: *mut LeanObject,
    mut v_acc_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_f_3147_, v_keys_3148_, v_vals_3149_, v_i_3150_, v_acc_3151_);
    lean_dec_ref(v_vals_3149_);
    lean_dec_ref(v_keys_3148_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(
    mut v_f_3153_: *mut LeanObject,
    mut v_x_3154_: *mut LeanObject,
    mut v_x_3155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: usize = 0;
    let mut v___x_3171_: usize = 0;
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: usize = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v_ks_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3154_) == 0 {
                    v_es_3156_ = lean_ctor_get(v_x_3154_, 0);
                    v_isSharedCheck_3176_ = (!lean_is_exclusive(v_x_3154_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3158_ = v_x_3154_;
                        v_isShared_3159_ = v_isSharedCheck_3176_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_3156_);
                        lean_dec(v_x_3154_);
                        v___x_3158_ = lean_box(0);
                        v_isShared_3159_ = v_isSharedCheck_3176_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_3177_ = lean_ctor_get(v_x_3154_, 0);
                    lean_inc_ref(v_ks_3177_);
                    v_vs_3178_ = lean_ctor_get(v_x_3154_, 1);
                    lean_inc_ref(v_vs_3178_);
                    lean_dec_ref_known(v_x_3154_, 2);
                    v___x_3179_ = lean_unsigned_to_nat(0);
                    v___x_3180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_f_3153_, v_ks_3177_, v_vs_3178_, v___x_3179_, v_x_3155_);
                    lean_dec_ref(v_vs_3178_);
                    lean_dec_ref(v_ks_3177_);
                    return v___x_3180_;
                }
            }
            1 => {
                v___x_3160_ = lean_unsigned_to_nat(0);
                v___x_3161_ = lean_array_get_size(v_es_3156_);
                v___x_3162_ = lean_nat_dec_lt(v___x_3160_, v___x_3161_);
                if v___x_3162_ == 0 {
                    lean_dec_ref(v_es_3156_);
                    lean_dec_ref(v_f_3153_);
                    if v_isShared_3159_ == 0 {
                        lean_ctor_set_tag(v___x_3158_, 1);
                        lean_ctor_set(v___x_3158_, 0, v_x_3155_);
                        v___x_3164_ = v___x_3158_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_x_3155_);
                        v___x_3164_ = v_reuseFailAlloc_3165_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3166_ = lean_nat_dec_le(v___x_3161_, v___x_3161_);
                    if v___x_3166_ == 0 {
                        if v___x_3162_ == 0 {
                            lean_dec_ref(v_es_3156_);
                            lean_dec_ref(v_f_3153_);
                            if v_isShared_3159_ == 0 {
                                lean_ctor_set_tag(v___x_3158_, 1);
                                lean_ctor_set(v___x_3158_, 0, v_x_3155_);
                                v___x_3168_ = v___x_3158_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_x_3155_);
                                v___x_3168_ = v_reuseFailAlloc_3169_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3158_);
                            v___x_3170_ = 0usize;
                            v___x_3171_ = lean_usize_of_nat(v___x_3161_);
                            v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3153_, v_es_3156_, v___x_3170_, v___x_3171_, v_x_3155_);
                            lean_dec_ref(v_es_3156_);
                            return v___x_3172_;
                        }
                    } else {
                        lean_del_object(v___x_3158_);
                        v___x_3173_ = 0usize;
                        v___x_3174_ = lean_usize_of_nat(v___x_3161_);
                        v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3153_, v_es_3156_, v___x_3173_, v___x_3174_, v_x_3155_);
                        lean_dec_ref(v_es_3156_);
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
    mut v_f_3181_: *mut LeanObject,
    mut v_as_3182_: *mut LeanObject,
    mut v_i_3183_: usize,
    mut v_stop_3184_: usize,
    mut v_b_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: usize = 0;
    let mut v___x_3189_: usize = 0;
    let mut v___y_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3194_ = lean_usize_dec_eq(v_i_3183_, v_stop_3184_);
                if v___x_3194_ == 0 {
                    v___x_3195_ = lean_array_uget_borrowed(v_as_3182_, v_i_3183_);
                    match lean_obj_tag(v___x_3195_) {
                        0 => {
                            v_key_3196_ = lean_ctor_get(v___x_3195_, 0);
                            v_val_3197_ = lean_ctor_get(v___x_3195_, 1);
                            lean_inc_ref(v_f_3181_);
                            lean_inc(v_val_3197_);
                            lean_inc(v_key_3196_);
                            v___x_3198_ =
                                lean_apply_3(v_f_3181_, v_b_3185_, v_key_3196_, v_val_3197_);
                            v___y_3192_ = v___x_3198_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_3199_ = lean_ctor_get(v___x_3195_, 0);
                            lean_inc(v_node_3199_);
                            lean_inc_ref(v_f_3181_);
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
                    lean_dec_ref(v_f_3181_);
                    v___x_3201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3201_, 0, v_b_3185_);
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
                if lean_obj_tag(v___y_3192_) == 0 {
                    lean_dec_ref(v_f_3181_);
                    return v___y_3192_;
                } else {
                    v_a_3193_ = lean_ctor_get(v___y_3192_, 0);
                    lean_inc(v_a_3193_);
                    lean_dec_ref_known(v___y_3192_, 1);
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
    mut v_f_3202_: *mut LeanObject,
    mut v_as_3203_: *mut LeanObject,
    mut v_i_3204_: *mut LeanObject,
    mut v_stop_3205_: *mut LeanObject,
    mut v_b_3206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3207_: usize = 0;
    let mut v_stop_boxed_3208_: usize = 0;
    let mut v_res_3209_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3207_ = lean_unbox_usize(v_i_3204_);
    lean_dec(v_i_3204_);
    v_stop_boxed_3208_ = lean_unbox_usize(v_stop_3205_);
    lean_dec(v_stop_3205_);
    v_res_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3202_, v_as_3203_, v_i_boxed_3207_, v_stop_boxed_3208_, v_b_3206_);
    lean_dec_ref(v_as_3203_);
    return v_res_3209_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(
    mut v_map_3210_: *mut LeanObject,
    mut v_init_3211_: *mut LeanObject,
    mut v_f_3212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut LeanObject = core::ptr::null_mut();
    v___f_3213_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_3213_, 0, v_f_3212_);
    lean_inc_ref(v_map_3210_);
    v___x_3214_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v___f_3213_, v_map_3210_, v_init_3211_);
    v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
    lean_inc(v_a_3215_);
    lean_dec_ref(v___x_3214_);
    return v_a_3215_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg___boxed(
    mut v_map_3216_: *mut LeanObject,
    mut v_init_3217_: *mut LeanObject,
    mut v_f_3218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3219_: *mut LeanObject = core::ptr::null_mut();
    v_res_3219_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(v_map_3216_, v_init_3217_, v_f_3218_);
    lean_dec_ref(v_map_3216_);
    return v_res_3219_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0(
    mut v_threshold_3220_: *mut LeanObject,
    mut v_p_3221_: *mut LeanObject,
    mut v_x_3222_: *mut LeanObject,
    mut v_____s_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    v_fst_3224_ = lean_ctor_get(v_x_3222_, 0);
    v_snd_3225_ = lean_ctor_get(v_x_3222_, 1);
    v___x_3226_ = lean_nat_dec_lt(v_threshold_3220_, v_snd_3225_);
    if v___x_3226_ == 0 {
        let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_3222_);
        lean_dec_ref(v_p_3221_);
        v___x_3227_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3227_, 0, v_____s_3223_);
        return v___x_3227_;
    } else {
        let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: u8 = 0;
        lean_inc(v_fst_3224_);
        v___x_3228_ = lean_apply_1(v_p_3221_, v_fst_3224_);
        v___x_3229_ = (lean_unbox(v___x_3228_) as u8);
        if v___x_3229_ == 0 {
            let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_x_3222_);
            v___x_3230_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3230_, 0, v_____s_3223_);
            return v___x_3230_;
        } else {
            let mut v_r_3231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
            v_r_3231_ = lean_array_push(v_____s_3223_, v_x_3222_);
            v___x_3232_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3232_, 0, v_r_3231_);
            return v___x_3232_;
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0___boxed(
    mut v_threshold_3233_: *mut LeanObject,
    mut v_p_3234_: *mut LeanObject,
    mut v_x_3235_: *mut LeanObject,
    mut v_____s_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3237_: *mut LeanObject = core::ptr::null_mut();
    v_res_3237_ =
        l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0(
            v_threshold_3233_,
            v_p_3234_,
            v_x_3235_,
            v_____s_3236_,
        );
    lean_dec(v_threshold_3233_);
    return v_res_3237_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1(
    mut v_counters_3240_: *mut LeanObject,
    mut v_threshold_3241_: *mut LeanObject,
    mut v_p_3242_: *mut LeanObject,
    mut v_lt_3243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3244_ = lean_alloc_closure(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_3244_, 0, v_threshold_3241_);
                lean_closure_set(v___f_3244_, 1, v_p_3242_);
                v___x_3245_ = lean_unsigned_to_nat(0);
                v_r_3246_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___closed__0;
                v___x_3247_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(v_counters_3240_, v_r_3246_, v___f_3244_);
                v___x_3248_ = lean_array_get_size(v___x_3247_);
                v___x_3249_ = lean_nat_dec_eq(v___x_3248_, v___x_3245_);
                if v___x_3249_ == 0 {
                    v___x_3250_ = lean_unsigned_to_nat(1);
                    v___x_3251_ = lean_nat_sub(v___x_3248_, v___x_3250_);
                    v___x_3257_ = lean_nat_dec_le(v___x_3245_, v___x_3251_);
                    if v___x_3257_ == 0 {
                        lean_inc(v___x_3251_);
                        v___y_3253_ = v___x_3251_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3253_ = v___x_3245_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_lt_3243_);
                    return v___x_3247_;
                }
            }
            1 => {
                v___x_3254_ = lean_nat_dec_le(v___y_3253_, v___x_3251_);
                if v___x_3254_ == 0 {
                    lean_dec(v___x_3251_);
                    lean_inc(v___y_3253_);
                    v___x_3255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3243_, v___x_3248_, v___x_3247_, v___y_3253_, v___y_3253_);
                    lean_dec(v___y_3253_);
                    return v___x_3255_;
                } else {
                    v___x_3256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3243_, v___x_3248_, v___x_3247_, v___y_3253_, v___x_3251_);
                    lean_dec(v___x_3251_);
                    return v___x_3256_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1___boxed(
    mut v_counters_3258_: *mut LeanObject,
    mut v_threshold_3259_: *mut LeanObject,
    mut v_p_3260_: *mut LeanObject,
    mut v_lt_3261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3262_: *mut LeanObject = core::ptr::null_mut();
    v_res_3262_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1(
        v_counters_3258_,
        v_threshold_3259_,
        v_p_3260_,
        v_lt_3261_,
    );
    lean_dec_ref(v_counters_3258_);
    return v_res_3262_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummary(
    mut v_cls_3267_: *mut LeanObject,
    mut v_counters_3268_: *mut LeanObject,
    mut v_p_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
    mut v_a_3271_: *mut LeanObject,
    mut v_a_3272_: *mut LeanObject,
    mut v_a_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3284_: usize = 0;
    let mut v___x_3285_: usize = 0;
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3303_: u8 = 0;
    let mut v_unused_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v_a_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3275_ = lean_ctor_get(v_a_3272_, 2);
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
                v___x_3281_ = lean_unsigned_to_nat(0);
                v___x_3282_ = lean_nat_dec_eq(v___x_3280_, v___x_3281_);
                if v___x_3282_ == 0 {
                    v___x_3283_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__0;
                    v_sz_3284_ = lean_array_size(v___x_3279_);
                    v___x_3285_ = 0usize;
                    v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3(v_cls_3267_, v___x_3279_, v_sz_3284_, v___x_3285_, v___x_3283_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
                    if lean_obj_tag(v___x_3286_) == 0 {
                        v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
                        v_isSharedCheck_3305_ = (!lean_is_exclusive(v___x_3286_)) as u8;
                        if v_isSharedCheck_3305_ == 0 {
                            v___x_3289_ = v___x_3286_;
                            v_isShared_3290_ = v_isSharedCheck_3305_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3287_);
                            lean_dec(v___x_3286_);
                            v___x_3289_ = lean_box(0);
                            v_isShared_3290_ = v_isSharedCheck_3305_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3279_);
                        v_a_3306_ = lean_ctor_get(v___x_3286_, 0);
                        v_isSharedCheck_3313_ = (!lean_is_exclusive(v___x_3286_)) as u8;
                        if v_isSharedCheck_3313_ == 0 {
                            v___x_3308_ = v___x_3286_;
                            v_isShared_3309_ = v_isSharedCheck_3313_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3306_);
                            lean_dec(v___x_3286_);
                            v___x_3308_ = lean_box(0);
                            v_isShared_3309_ = v_isSharedCheck_3313_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3279_);
                    lean_dec(v_cls_3267_);
                    v___x_3314_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__1;
                    v___x_3315_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3315_, 0, v___x_3314_);
                    return v___x_3315_;
                }
            }
            1 => {
                v___x_3291_ = l_Lean_Meta_mkDiagSummary___closed__1;
                v___x_3292_ = lean_array_get(v___x_3291_, v___x_3279_, v___x_3281_);
                lean_dec_ref(v___x_3279_);
                v_snd_3293_ = lean_ctor_get(v___x_3292_, 1);
                v_isSharedCheck_3303_ = (!lean_is_exclusive(v___x_3292_)) as u8;
                if v_isSharedCheck_3303_ == 0 {
                    v_unused_3304_ = lean_ctor_get(v___x_3292_, 0);
                    lean_dec(v_unused_3304_);
                    v___x_3295_ = v___x_3292_;
                    v_isShared_3296_ = v_isSharedCheck_3303_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3293_);
                    lean_dec(v___x_3292_);
                    v___x_3295_ = lean_box(0);
                    v_isShared_3296_ = v_isSharedCheck_3303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3296_ == 0 {
                    lean_ctor_set(v___x_3295_, 0, v_a_3287_);
                    v___x_3298_ = v___x_3295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3287_);
                    lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_snd_3293_);
                    v___x_3298_ = v_reuseFailAlloc_3302_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3290_ == 0 {
                    lean_ctor_set(v___x_3289_, 0, v___x_3298_);
                    v___x_3300_ = v___x_3289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
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
                    v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
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
    mut v_cls_3316_: *mut LeanObject,
    mut v_counters_3317_: *mut LeanObject,
    mut v_p_3318_: *mut LeanObject,
    mut v_a_3319_: *mut LeanObject,
    mut v_a_3320_: *mut LeanObject,
    mut v_a_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3324_: *mut LeanObject = core::ptr::null_mut();
    v_res_3324_ = l_Lean_Meta_mkDiagSummary(
        v_cls_3316_,
        v_counters_3317_,
        v_p_3318_,
        v_a_3319_,
        v_a_3320_,
        v_a_3321_,
        v_a_3322_,
    );
    lean_dec(v_a_3322_);
    lean_dec_ref(v_a_3321_);
    lean_dec(v_a_3320_);
    lean_dec_ref(v_a_3319_);
    lean_dec_ref(v_counters_3317_);
    return v_res_3324_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1(
    mut v_00_u03c3_3325_: *mut LeanObject,
    mut v_00_u03b2_3326_: *mut LeanObject,
    mut v_map_3327_: *mut LeanObject,
    mut v_init_3328_: *mut LeanObject,
    mut v_f_3329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___redArg(v_map_3327_, v_init_3328_, v_f_3329_);
    return v___x_3330_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1___boxed(
    mut v_00_u03c3_3331_: *mut LeanObject,
    mut v_00_u03b2_3332_: *mut LeanObject,
    mut v_map_3333_: *mut LeanObject,
    mut v_init_3334_: *mut LeanObject,
    mut v_f_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3336_: *mut LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1(v_00_u03c3_3331_, v_00_u03b2_3332_, v_map_3333_, v_init_3334_, v_f_3335_);
    lean_dec_ref(v_map_3333_);
    return v_res_3336_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2(
    mut v_lt_3337_: *mut LeanObject,
    mut v_n_3338_: *mut LeanObject,
    mut v_as_3339_: *mut LeanObject,
    mut v_lo_3340_: *mut LeanObject,
    mut v_hi_3341_: *mut LeanObject,
    mut v_w_3342_: *mut LeanObject,
    mut v_hlo_3343_: *mut LeanObject,
    mut v_hhi_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    v___x_3345_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___redArg(v_lt_3337_, v_n_3338_, v_as_3339_, v_lo_3340_, v_hi_3341_);
    return v___x_3345_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2___boxed(
    mut v_lt_3346_: *mut LeanObject,
    mut v_n_3347_: *mut LeanObject,
    mut v_as_3348_: *mut LeanObject,
    mut v_lo_3349_: *mut LeanObject,
    mut v_hi_3350_: *mut LeanObject,
    mut v_w_3351_: *mut LeanObject,
    mut v_hlo_3352_: *mut LeanObject,
    mut v_hhi_3353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3354_: *mut LeanObject = core::ptr::null_mut();
    v_res_3354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2(v_lt_3346_, v_n_3347_, v_as_3348_, v_lo_3349_, v_hi_3350_, v_w_3351_, v_hlo_3352_, v_hhi_3353_);
    lean_dec(v_hi_3350_);
    lean_dec(v_n_3347_);
    return v_res_3354_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2___redArg(
    mut v_map_3355_: *mut LeanObject,
    mut v_f_3356_: *mut LeanObject,
    mut v_init_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_3356_, v_map_3355_, v_init_3357_);
    return v___x_3358_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2(
    mut v_00_u03c3_3359_: *mut LeanObject,
    mut v_00_u03c3_3360_: *mut LeanObject,
    mut v_00_u03b2_3361_: *mut LeanObject,
    mut v_map_3362_: *mut LeanObject,
    mut v_f_3363_: *mut LeanObject,
    mut v_init_3364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    v___x_3365_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_3363_, v_map_3362_, v_init_3364_);
    return v___x_3365_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4(
    mut v_lt_3366_: *mut LeanObject,
    mut v_n_3367_: *mut LeanObject,
    mut v_lo_3368_: *mut LeanObject,
    mut v_hi_3369_: *mut LeanObject,
    mut v_hhi_3370_: *mut LeanObject,
    mut v_pivot_3371_: *mut LeanObject,
    mut v_as_3372_: *mut LeanObject,
    mut v_i_3373_: *mut LeanObject,
    mut v_k_3374_: *mut LeanObject,
    mut v_ilo_3375_: *mut LeanObject,
    mut v_ik_3376_: *mut LeanObject,
    mut v_w_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3378_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_3366_, v_hi_3369_, v_pivot_3371_, v_as_3372_, v_i_3373_, v_k_3374_);
    return v___x_3378_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4___boxed(
    mut v_lt_3379_: *mut LeanObject,
    mut v_n_3380_: *mut LeanObject,
    mut v_lo_3381_: *mut LeanObject,
    mut v_hi_3382_: *mut LeanObject,
    mut v_hhi_3383_: *mut LeanObject,
    mut v_pivot_3384_: *mut LeanObject,
    mut v_as_3385_: *mut LeanObject,
    mut v_i_3386_: *mut LeanObject,
    mut v_k_3387_: *mut LeanObject,
    mut v_ilo_3388_: *mut LeanObject,
    mut v_ik_3389_: *mut LeanObject,
    mut v_w_3390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3391_: *mut LeanObject = core::ptr::null_mut();
    v_res_3391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__2_spec__4(v_lt_3379_, v_n_3380_, v_lo_3381_, v_hi_3382_, v_hhi_3383_, v_pivot_3384_, v_as_3385_, v_i_3386_, v_k_3387_, v_ilo_3388_, v_ik_3389_, v_w_3390_);
    lean_dec(v_hi_3382_);
    lean_dec(v_lo_3381_);
    lean_dec(v_n_3380_);
    return v_res_3391_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7(
    mut v_00_u03b1_3392_: *mut LeanObject,
    mut v_constName_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___redArg(v_constName_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b1_3400_: *mut LeanObject,
    mut v_constName_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3407_: *mut LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7(v_00_u03b1_3400_, v_constName_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
    lean_dec(v___y_3405_);
    lean_dec_ref(v___y_3404_);
    lean_dec(v___y_3403_);
    lean_dec_ref(v___y_3402_);
    return v_res_3407_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5(
    mut v_00_u03c3_3408_: *mut LeanObject,
    mut v_00_u03c3_3409_: *mut LeanObject,
    mut v_00_u03b1_3410_: *mut LeanObject,
    mut v_00_u03b2_3411_: *mut LeanObject,
    mut v_f_3412_: *mut LeanObject,
    mut v_x_3413_: *mut LeanObject,
    mut v_x_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_3412_, v_x_3413_, v_x_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10(
    mut v_00_u03b1_3416_: *mut LeanObject,
    mut v_ref_3417_: *mut LeanObject,
    mut v_constName_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___redArg(v_ref_3417_, v_constName_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
    return v___x_3424_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10___boxed(
    mut v_00_u03b1_3425_: *mut LeanObject,
    mut v_ref_3426_: *mut LeanObject,
    mut v_constName_3427_: *mut LeanObject,
    mut v___y_3428_: *mut LeanObject,
    mut v___y_3429_: *mut LeanObject,
    mut v___y_3430_: *mut LeanObject,
    mut v___y_3431_: *mut LeanObject,
    mut v___y_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3433_: *mut LeanObject = core::ptr::null_mut();
    v_res_3433_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_3425_, v_ref_3426_, v_constName_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
    lean_dec(v___y_3431_);
    lean_dec_ref(v___y_3430_);
    lean_dec(v___y_3429_);
    lean_dec_ref(v___y_3428_);
    lean_dec(v_ref_3426_);
    return v_res_3433_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(
    mut v_00_u03b1_3434_: *mut LeanObject,
    mut v_00_u03b2_3435_: *mut LeanObject,
    mut v_00_u03c3_3436_: *mut LeanObject,
    mut v_00_u03c3_3437_: *mut LeanObject,
    mut v_f_3438_: *mut LeanObject,
    mut v_as_3439_: *mut LeanObject,
    mut v_i_3440_: usize,
    mut v_stop_3441_: usize,
    mut v_b_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_3438_, v_as_3439_, v_i_3440_, v_stop_3441_, v_b_3442_);
    return v___x_3443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(
    mut v_00_u03b1_3444_: *mut LeanObject,
    mut v_00_u03b2_3445_: *mut LeanObject,
    mut v_00_u03c3_3446_: *mut LeanObject,
    mut v_00_u03c3_3447_: *mut LeanObject,
    mut v_f_3448_: *mut LeanObject,
    mut v_as_3449_: *mut LeanObject,
    mut v_i_3450_: *mut LeanObject,
    mut v_stop_3451_: *mut LeanObject,
    mut v_b_3452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3453_: usize = 0;
    let mut v_stop_boxed_3454_: usize = 0;
    let mut v_res_3455_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3453_ = lean_unbox_usize(v_i_3450_);
    lean_dec(v_i_3450_);
    v_stop_boxed_3454_ = lean_unbox_usize(v_stop_3451_);
    lean_dec(v_stop_3451_);
    v_res_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(v_00_u03b1_3444_, v_00_u03b2_3445_, v_00_u03c3_3446_, v_00_u03c3_3447_, v_f_3448_, v_as_3449_, v_i_boxed_3453_, v_stop_boxed_3454_, v_b_3452_);
    lean_dec_ref(v_as_3449_);
    return v_res_3455_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10(
    mut v_00_u03c3_3456_: *mut LeanObject,
    mut v_00_u03c3_3457_: *mut LeanObject,
    mut v_00_u03b1_3458_: *mut LeanObject,
    mut v_00_u03b2_3459_: *mut LeanObject,
    mut v_f_3460_: *mut LeanObject,
    mut v_keys_3461_: *mut LeanObject,
    mut v_vals_3462_: *mut LeanObject,
    mut v_heq_3463_: *mut LeanObject,
    mut v_i_3464_: *mut LeanObject,
    mut v_acc_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    v___x_3466_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___redArg(v_f_3460_, v_keys_3461_, v_vals_3462_, v_i_3464_, v_acc_3465_);
    return v___x_3466_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(
    mut v_00_u03c3_3467_: *mut LeanObject,
    mut v_00_u03c3_3468_: *mut LeanObject,
    mut v_00_u03b1_3469_: *mut LeanObject,
    mut v_00_u03b2_3470_: *mut LeanObject,
    mut v_f_3471_: *mut LeanObject,
    mut v_keys_3472_: *mut LeanObject,
    mut v_vals_3473_: *mut LeanObject,
    mut v_heq_3474_: *mut LeanObject,
    mut v_i_3475_: *mut LeanObject,
    mut v_acc_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3477_: *mut LeanObject = core::ptr::null_mut();
    v_res_3477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_mkDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__10(v_00_u03c3_3467_, v_00_u03c3_3468_, v_00_u03b1_3469_, v_00_u03b2_3470_, v_f_3471_, v_keys_3472_, v_vals_3473_, v_heq_3474_, v_i_3475_, v_acc_3476_);
    lean_dec_ref(v_vals_3473_);
    lean_dec_ref(v_keys_3472_);
    return v_res_3477_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14(
    mut v_00_u03b1_3478_: *mut LeanObject,
    mut v_ref_3479_: *mut LeanObject,
    mut v_msg_3480_: *mut LeanObject,
    mut v_declHint_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___redArg(v_ref_3479_, v_msg_3480_, v_declHint_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14___boxed(
    mut v_00_u03b1_3488_: *mut LeanObject,
    mut v_ref_3489_: *mut LeanObject,
    mut v_msg_3490_: *mut LeanObject,
    mut v_declHint_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3497_: *mut LeanObject = core::ptr::null_mut();
    v_res_3497_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14(v_00_u03b1_3488_, v_ref_3489_, v_msg_3490_, v_declHint_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
    lean_dec(v___y_3495_);
    lean_dec_ref(v___y_3494_);
    lean_dec(v___y_3493_);
    lean_dec_ref(v___y_3492_);
    lean_dec(v_ref_3489_);
    return v_res_3497_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16(
    mut v_msg_3498_: *mut LeanObject,
    mut v_declHint_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___redArg(v_msg_3498_, v_declHint_3499_, v___y_3503_);
    return v___x_3505_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16___boxed(
    mut v_msg_3506_: *mut LeanObject,
    mut v_declHint_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3513_: *mut LeanObject = core::ptr::null_mut();
    v_res_3513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__15_spec__16(v_msg_3506_, v_declHint_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
    lean_dec(v___y_3511_);
    lean_dec_ref(v___y_3510_);
    lean_dec(v___y_3509_);
    lean_dec_ref(v___y_3508_);
    return v_res_3513_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16(
    mut v_00_u03b1_3514_: *mut LeanObject,
    mut v_ref_3515_: *mut LeanObject,
    mut v_msg_3516_: *mut LeanObject,
    mut v___y_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    v___x_3522_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___redArg(v_ref_3515_, v_msg_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
    return v___x_3522_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16___boxed(
    mut v_00_u03b1_3523_: *mut LeanObject,
    mut v_ref_3524_: *mut LeanObject,
    mut v_msg_3525_: *mut LeanObject,
    mut v___y_3526_: *mut LeanObject,
    mut v___y_3527_: *mut LeanObject,
    mut v___y_3528_: *mut LeanObject,
    mut v___y_3529_: *mut LeanObject,
    mut v___y_3530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3531_: *mut LeanObject = core::ptr::null_mut();
    v_res_3531_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16(v_00_u03b1_3523_, v_ref_3524_, v_msg_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
    lean_dec(v___y_3529_);
    lean_dec_ref(v___y_3528_);
    lean_dec(v___y_3527_);
    lean_dec_ref(v___y_3526_);
    lean_dec(v_ref_3524_);
    return v_res_3531_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18(
    mut v_00_u03b1_3532_: *mut LeanObject,
    mut v_msg_3533_: *mut LeanObject,
    mut v___y_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    v___x_3539_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___redArg(v_msg_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
    return v___x_3539_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18___boxed(
    mut v_00_u03b1_3540_: *mut LeanObject,
    mut v_msg_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3547_: *mut LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_3540_, v_msg_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
    lean_dec(v___y_3545_);
    lean_dec_ref(v___y_3544_);
    lean_dec(v___y_3543_);
    lean_dec_ref(v___y_3542_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0(
    mut v_env_3548_: *mut LeanObject,
    mut v_instances_3549_: u8,
    mut v_declName_3550_: *mut LeanObject,
) -> u8 {
    let mut v___x_3551_: u8 = 0;
    lean_inc(v_declName_3550_);
    lean_inc_ref(v_env_3548_);
    v___x_3551_ = lean_get_reducibility_status(v_env_3548_, v_declName_3550_);
    if v___x_3551_ == 1 {
        let mut v___x_3552_: u8 = 0;
        v___x_3552_ = l_Lean_Meta_isInstanceCore(v_env_3548_, v_declName_3550_);
        lean_dec(v_declName_3550_);
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
        lean_dec(v_declName_3550_);
        lean_dec_ref(v_env_3548_);
        v___x_3554_ = 0;
        return v___x_3554_;
    }
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0___boxed(
    mut v_env_3555_: *mut LeanObject,
    mut v_instances_3556_: *mut LeanObject,
    mut v_declName_3557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_instances_boxed_3558_: u8 = 0;
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut LeanObject = core::ptr::null_mut();
    v_instances_boxed_3558_ = (lean_unbox(v_instances_3556_) as u8);
    v_res_3559_ = l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0(
        v_env_3555_,
        v_instances_boxed_3558_,
        v_declName_3557_,
    );
    v_r_3560_ = lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfolded(
    mut v_counters_3564_: *mut LeanObject,
    mut v_instances_3565_: u8,
    mut v_a_3566_: *mut LeanObject,
    mut v_a_3567_: *mut LeanObject,
    mut v_a_3568_: *mut LeanObject,
    mut v_a_3569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    v___x_3571_ = lean_st_ref_get(v_a_3569_);
    v_env_3572_ = lean_ctor_get(v___x_3571_, 0);
    lean_inc_ref(v_env_3572_);
    lean_dec(v___x_3571_);
    v___x_3573_ = lean_box((v_instances_3565_) as usize);
    v___f_3574_ = lean_alloc_closure(
        l_Lean_Meta_mkDiagSummaryForUnfolded___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3574_, 0, v_env_3572_);
    lean_closure_set(v___f_3574_, 1, v___x_3573_);
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
    mut v_counters_3577_: *mut LeanObject,
    mut v_instances_3578_: *mut LeanObject,
    mut v_a_3579_: *mut LeanObject,
    mut v_a_3580_: *mut LeanObject,
    mut v_a_3581_: *mut LeanObject,
    mut v_a_3582_: *mut LeanObject,
    mut v_a_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_instances_boxed_3584_: u8 = 0;
    let mut v_res_3585_: *mut LeanObject = core::ptr::null_mut();
    v_instances_boxed_3584_ = (lean_unbox(v_instances_3578_) as u8);
    v_res_3585_ = l_Lean_Meta_mkDiagSummaryForUnfolded(
        v_counters_3577_,
        v_instances_boxed_3584_,
        v_a_3579_,
        v_a_3580_,
        v_a_3581_,
        v_a_3582_,
    );
    lean_dec(v_a_3582_);
    lean_dec_ref(v_a_3581_);
    lean_dec(v_a_3580_);
    lean_dec_ref(v_a_3579_);
    lean_dec_ref(v_counters_3577_);
    return v_res_3585_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lam__0(
    mut v_env_3586_: *mut LeanObject,
    mut v_declName_3587_: *mut LeanObject,
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
    mut v_env_3591_: *mut LeanObject,
    mut v_declName_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3593_: u8 = 0;
    let mut v_r_3594_: *mut LeanObject = core::ptr::null_mut();
    v_res_3593_ =
        l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lam__0(v_env_3591_, v_declName_3592_);
    v_r_3594_ = lean_box((v_res_3593_) as usize);
    return v_r_3594_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(
    mut v_counters_3595_: *mut LeanObject,
    mut v_a_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    v___x_3601_ = lean_st_ref_get(v_a_3599_);
    v_env_3602_ = lean_ctor_get(v___x_3601_, 0);
    lean_inc_ref(v_env_3602_);
    lean_dec(v___x_3601_);
    v___f_3603_ = lean_alloc_closure(
        l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3603_, 0, v_env_3602_);
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
    mut v_counters_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3612_: *mut LeanObject = core::ptr::null_mut();
    v_res_3612_ = l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(
        v_counters_3606_,
        v_a_3607_,
        v_a_3608_,
        v_a_3609_,
        v_a_3610_,
    );
    lean_dec(v_a_3610_);
    lean_dec_ref(v_a_3609_);
    lean_dec(v_a_3608_);
    lean_dec_ref(v_a_3607_);
    lean_dec_ref(v_counters_3606_);
    return v_res_3612_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0(
    mut v_x_3613_: *mut LeanObject,
) -> u8 {
    let mut v___x_3614_: u8 = 0;
    v___x_3614_ = 1;
    return v___x_3614_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0___boxed(
    mut v_x_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3616_: u8 = 0;
    let mut v_r_3617_: *mut LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_Meta_mkDiagSummaryForUsedInstances___lam__0(v_x_3615_);
    lean_dec(v_x_3615_);
    v_r_3617_ = lean_box((v_res_3616_) as usize);
    return v_r_3617_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances(
    mut v_a_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
    mut v_a_3625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instanceCounter_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    v___x_3627_ = lean_st_ref_get(v_a_3623_);
    v_diag_3628_ = lean_ctor_get(v___x_3627_, 4);
    lean_inc_ref(v_diag_3628_);
    lean_dec(v___x_3627_);
    v_instanceCounter_3629_ = lean_ctor_get(v_diag_3628_, 3);
    lean_inc_ref(v_instanceCounter_3629_);
    lean_dec_ref(v_diag_3628_);
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
    lean_dec_ref(v_instanceCounter_3629_);
    return v___x_3632_;
}
pub unsafe fn l_Lean_Meta_mkDiagSummaryForUsedInstances___boxed(
    mut v_a_3633_: *mut LeanObject,
    mut v_a_3634_: *mut LeanObject,
    mut v_a_3635_: *mut LeanObject,
    mut v_a_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3638_: *mut LeanObject = core::ptr::null_mut();
    v_res_3638_ =
        l_Lean_Meta_mkDiagSummaryForUsedInstances(v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
    lean_dec(v_a_3636_);
    lean_dec_ref(v_a_3635_);
    lean_dec(v_a_3634_);
    lean_dec_ref(v_a_3633_);
    return v_res_3638_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___redArg(
    mut v_x_3639_: *mut LeanObject,
) -> u8 {
    let mut v___x_3640_: u8 = 0;
    v___x_3640_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_3639_);
    return v___x_3640_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___redArg___boxed(
    mut v_x_3641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3642_: u8 = 0;
    let mut v_r_3643_: *mut LeanObject = core::ptr::null_mut();
    v_res_3642_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___redArg(v_x_3641_);
    lean_dec_ref(v_x_3641_);
    v_r_3643_ = lean_box((v_res_3642_) as usize);
    return v_r_3643_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0(
    mut v_00_u03b2_3644_: *mut LeanObject,
    mut v_x_3645_: *mut LeanObject,
) -> u8 {
    let mut v___x_3646_: u8 = 0;
    v___x_3646_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_3645_);
    return v___x_3646_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0___boxed(
    mut v_00_u03b2_3647_: *mut LeanObject,
    mut v_x_3648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3649_: u8 = 0;
    let mut v_r_3650_: *mut LeanObject = core::ptr::null_mut();
    v_res_3649_ =
        l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__0(
            v_00_u03b2_3647_,
            v_x_3648_,
        );
    lean_dec_ref(v_x_3648_);
    v_r_3650_ = lean_box((v_res_3649_) as usize);
    return v_r_3650_;
}
pub unsafe fn l_Lean_Meta_mkDiagSynthPendingFailure___lam__0(
    mut v___x_3651_: *mut LeanObject,
    mut v___x_3652_: u8,
    mut v_data_3653_: *mut LeanObject,
    mut v_x_3654_: *mut LeanObject,
    mut v_____s_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: f64 = 0.0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    v_snd_3661_ = lean_ctor_get(v_x_3654_, 1);
    v___x_3662_ = l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__2;
    v___x_3663_ = lean_box(0);
    v___x_3664_ = lean_float_of_nat(v___x_3651_);
    v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
    v___x_3666_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_3666_, 0, v___x_3662_);
    lean_ctor_set(v___x_3666_, 1, v___x_3663_);
    lean_ctor_set(v___x_3666_, 2, v___x_3665_);
    lean_ctor_set_float(
        v___x_3666_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3664_,
    );
    lean_ctor_set_float(
        v___x_3666_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_3664_,
    );
    lean_ctor_set_uint8(
        v___x_3666_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_3652_,
    );
    lean_inc(v_snd_3661_);
    v___x_3667_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    lean_ctor_set(v___x_3667_, 1, v_snd_3661_);
    lean_ctor_set(v___x_3667_, 2, v_data_3653_);
    v_data_3668_ = lean_array_push(v_____s_3655_, v___x_3667_);
    v___x_3669_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3669_, 0, v_data_3668_);
    v___x_3670_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3670_, 0, v___x_3669_);
    return v___x_3670_;
}
pub unsafe fn l_Lean_Meta_mkDiagSynthPendingFailure___lam__0___boxed(
    mut v___x_3671_: *mut LeanObject,
    mut v___x_3672_: *mut LeanObject,
    mut v_data_3673_: *mut LeanObject,
    mut v_x_3674_: *mut LeanObject,
    mut v_____s_3675_: *mut LeanObject,
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2636__boxed_3681_: u8 = 0;
    let mut v_res_3682_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636__boxed_3681_ = (lean_unbox(v___x_3672_) as u8);
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
    lean_dec(v___y_3679_);
    lean_dec_ref(v___y_3678_);
    lean_dec(v___y_3677_);
    lean_dec_ref(v___y_3676_);
    lean_dec_ref(v_x_3674_);
    return v_res_3682_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___lam__0(
    mut v_f_3683_: *mut LeanObject,
    mut v_s_3684_: *mut LeanObject,
    mut v_a_3685_: *mut LeanObject,
    mut v_b_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v_a_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3701_: u8 = 0;
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_a_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3692_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3692_, 0, v_a_3685_);
                lean_ctor_set(v___x_3692_, 1, v_b_3686_);
                lean_inc(v___y_3690_);
                lean_inc_ref(v___y_3689_);
                lean_inc(v___y_3688_);
                lean_inc_ref(v___y_3687_);
                v___x_3693_ = lean_apply_7(
                    v_f_3683_,
                    v___x_3692_,
                    v_s_3684_,
                    v___y_3687_,
                    v___y_3688_,
                    v___y_3689_,
                    v___y_3690_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3693_) == 0 {
                    v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
                    v_isSharedCheck_3720_ = (!lean_is_exclusive(v___x_3693_)) as u8;
                    if v_isSharedCheck_3720_ == 0 {
                        v___x_3696_ = v___x_3693_;
                        v_isShared_3697_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3694_);
                        lean_dec(v___x_3693_);
                        v___x_3696_ = lean_box(0);
                        v_isShared_3697_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3721_ = lean_ctor_get(v___x_3693_, 0);
                    v_isSharedCheck_3728_ = (!lean_is_exclusive(v___x_3693_)) as u8;
                    if v_isSharedCheck_3728_ == 0 {
                        v___x_3723_ = v___x_3693_;
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3721_);
                        lean_dec(v___x_3693_);
                        v___x_3723_ = lean_box(0);
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3694_) == 0 {
                    v_a_3698_ = lean_ctor_get(v_a_3694_, 0);
                    v_isSharedCheck_3708_ = (!lean_is_exclusive(v_a_3694_)) as u8;
                    if v_isSharedCheck_3708_ == 0 {
                        v___x_3700_ = v_a_3694_;
                        v_isShared_3701_ = v_isSharedCheck_3708_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3698_);
                        lean_dec(v_a_3694_);
                        v___x_3700_ = lean_box(0);
                        v_isShared_3701_ = v_isSharedCheck_3708_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3709_ = lean_ctor_get(v_a_3694_, 0);
                    v_isSharedCheck_3719_ = (!lean_is_exclusive(v_a_3694_)) as u8;
                    if v_isSharedCheck_3719_ == 0 {
                        v___x_3711_ = v_a_3694_;
                        v_isShared_3712_ = v_isSharedCheck_3719_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3709_);
                        lean_dec(v_a_3694_);
                        v___x_3711_ = lean_box(0);
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
                    v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3698_);
                    v___x_3703_ = v_reuseFailAlloc_3707_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3697_ == 0 {
                    lean_ctor_set(v___x_3696_, 0, v___x_3703_);
                    v___x_3705_ = v___x_3696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
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
                    v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3709_);
                    v___x_3714_ = v_reuseFailAlloc_3718_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3697_ == 0 {
                    lean_ctor_set(v___x_3696_, 0, v___x_3714_);
                    v___x_3716_ = v___x_3696_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
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
                    v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
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
    mut v_f_3729_: *mut LeanObject,
    mut v_s_3730_: *mut LeanObject,
    mut v_a_3731_: *mut LeanObject,
    mut v_b_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
    mut v___y_3734_: *mut LeanObject,
    mut v___y_3735_: *mut LeanObject,
    mut v___y_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3738_: *mut LeanObject = core::ptr::null_mut();
    v_res_3738_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___lam__0(v_f_3729_, v_s_3730_, v_a_3731_, v_b_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
    lean_dec(v___y_3736_);
    lean_dec_ref(v___y_3735_);
    lean_dec(v___y_3734_);
    lean_dec_ref(v___y_3733_);
    return v_res_3738_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_f_3739_: *mut LeanObject,
    mut v_keys_3740_: *mut LeanObject,
    mut v_vals_3741_: *mut LeanObject,
    mut v_i_3742_: *mut LeanObject,
    mut v_acc_3743_: *mut LeanObject,
    mut v___y_3744_: *mut LeanObject,
    mut v___y_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3749_ = lean_array_get_size(v_keys_3740_);
                v___x_3750_ = lean_nat_dec_lt(v_i_3742_, v___x_3749_);
                if v___x_3750_ == 0 {
                    lean_dec(v_i_3742_);
                    lean_dec_ref(v_f_3739_);
                    v___x_3751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3751_, 0, v_acc_3743_);
                    v___x_3752_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3752_, 0, v___x_3751_);
                    return v___x_3752_;
                } else {
                    v_k_3753_ = lean_array_fget_borrowed(v_keys_3740_, v_i_3742_);
                    v_v_3754_ = lean_array_fget_borrowed(v_vals_3741_, v_i_3742_);
                    lean_inc_ref(v_f_3739_);
                    lean_inc(v___y_3747_);
                    lean_inc_ref(v___y_3746_);
                    lean_inc(v___y_3745_);
                    lean_inc_ref(v___y_3744_);
                    lean_inc(v_v_3754_);
                    lean_inc(v_k_3753_);
                    v___x_3755_ = lean_apply_8(
                        v_f_3739_,
                        v_acc_3743_,
                        v_k_3753_,
                        v_v_3754_,
                        v___y_3744_,
                        v___y_3745_,
                        v___y_3746_,
                        v___y_3747_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3755_) == 0 {
                        v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
                        lean_inc(v_a_3756_);
                        if lean_obj_tag(v_a_3756_) == 0 {
                            lean_dec_ref_known(v_a_3756_, 1);
                            lean_dec(v_i_3742_);
                            lean_dec_ref(v_f_3739_);
                            return v___x_3755_;
                        } else {
                            lean_dec_ref_known(v___x_3755_, 1);
                            v_a_3757_ = lean_ctor_get(v_a_3756_, 0);
                            lean_inc(v_a_3757_);
                            lean_dec_ref_known(v_a_3756_, 1);
                            v___x_3758_ = lean_unsigned_to_nat(1);
                            v___x_3759_ = lean_nat_add(v_i_3742_, v___x_3758_);
                            lean_dec(v_i_3742_);
                            v_i_3742_ = v___x_3759_;
                            v_acc_3743_ = v_a_3757_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_3742_);
                        lean_dec_ref(v_f_3739_);
                        return v___x_3755_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_f_3761_: *mut LeanObject,
    mut v_keys_3762_: *mut LeanObject,
    mut v_vals_3763_: *mut LeanObject,
    mut v_i_3764_: *mut LeanObject,
    mut v_acc_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
    mut v___y_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3771_: *mut LeanObject = core::ptr::null_mut();
    v_res_3771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3761_, v_keys_3762_, v_vals_3763_, v_i_3764_, v_acc_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
    lean_dec(v___y_3769_);
    lean_dec_ref(v___y_3768_);
    lean_dec(v___y_3767_);
    lean_dec_ref(v___y_3766_);
    lean_dec_ref(v_vals_3763_);
    lean_dec_ref(v_keys_3762_);
    return v_res_3771_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(
    mut v_f_3772_: *mut LeanObject,
    mut v_x_3773_: *mut LeanObject,
    mut v_x_3774_: *mut LeanObject,
    mut v___y_3775_: *mut LeanObject,
    mut v___y_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: usize = 0;
    let mut v___x_3800_: usize = 0;
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_ks_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3773_) == 0 {
                    v_es_3780_ = lean_ctor_get(v_x_3773_, 0);
                    v_isSharedCheck_3802_ = (!lean_is_exclusive(v_x_3773_)) as u8;
                    if v_isSharedCheck_3802_ == 0 {
                        v___x_3782_ = v_x_3773_;
                        v_isShared_3783_ = v_isSharedCheck_3802_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_3780_);
                        lean_dec(v_x_3773_);
                        v___x_3782_ = lean_box(0);
                        v_isShared_3783_ = v_isSharedCheck_3802_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_3803_ = lean_ctor_get(v_x_3773_, 0);
                    lean_inc_ref(v_ks_3803_);
                    v_vs_3804_ = lean_ctor_get(v_x_3773_, 1);
                    lean_inc_ref(v_vs_3804_);
                    lean_dec_ref_known(v_x_3773_, 2);
                    v___x_3805_ = lean_unsigned_to_nat(0);
                    v___x_3806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(v_f_3772_, v_ks_3803_, v_vs_3804_, v___x_3805_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
                    lean_dec_ref(v_vs_3804_);
                    lean_dec_ref(v_ks_3803_);
                    return v___x_3806_;
                }
            }
            1 => {
                v___x_3784_ = lean_unsigned_to_nat(0);
                v___x_3785_ = lean_array_get_size(v_es_3780_);
                v___x_3786_ = lean_nat_dec_lt(v___x_3784_, v___x_3785_);
                if v___x_3786_ == 0 {
                    lean_dec_ref(v_es_3780_);
                    lean_dec_ref(v_f_3772_);
                    if v_isShared_3783_ == 0 {
                        lean_ctor_set_tag(v___x_3782_, 1);
                        lean_ctor_set(v___x_3782_, 0, v_x_3774_);
                        v___x_3788_ = v___x_3782_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_x_3774_);
                        v___x_3788_ = v_reuseFailAlloc_3790_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3791_ = lean_nat_dec_le(v___x_3785_, v___x_3785_);
                    if v___x_3791_ == 0 {
                        if v___x_3786_ == 0 {
                            lean_dec_ref(v_es_3780_);
                            lean_dec_ref(v_f_3772_);
                            if v_isShared_3783_ == 0 {
                                lean_ctor_set_tag(v___x_3782_, 1);
                                lean_ctor_set(v___x_3782_, 0, v_x_3774_);
                                v___x_3793_ = v___x_3782_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_x_3774_);
                                v___x_3793_ = v_reuseFailAlloc_3795_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3782_);
                            v___x_3796_ = 0usize;
                            v___x_3797_ = lean_usize_of_nat(v___x_3785_);
                            v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3772_, v_es_3780_, v___x_3796_, v___x_3797_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
                            lean_dec_ref(v_es_3780_);
                            return v___x_3798_;
                        }
                    } else {
                        lean_del_object(v___x_3782_);
                        v___x_3799_ = 0usize;
                        v___x_3800_ = lean_usize_of_nat(v___x_3785_);
                        v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3772_, v_es_3780_, v___x_3799_, v___x_3800_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
                        lean_dec_ref(v_es_3780_);
                        return v___x_3801_;
                    }
                }
            }
            2 => {
                v___x_3789_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3789_, 0, v___x_3788_);
                return v___x_3789_;
            }
            3 => {
                v___x_3794_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3794_, 0, v___x_3793_);
                return v___x_3794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_f_3807_: *mut LeanObject,
    mut v_as_3808_: *mut LeanObject,
    mut v_i_3809_: usize,
    mut v_stop_3810_: usize,
    mut v_b_3811_: *mut LeanObject,
    mut v___y_3812_: *mut LeanObject,
    mut v___y_3813_: *mut LeanObject,
    mut v___y_3814_: *mut LeanObject,
    mut v___y_3815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: usize = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___y_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: u8 = 0;
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3826_ = lean_usize_dec_eq(v_i_3809_, v_stop_3810_);
                if v___x_3826_ == 0 {
                    v___x_3827_ = lean_array_uget_borrowed(v_as_3808_, v_i_3809_);
                    match lean_obj_tag(v___x_3827_) {
                        0 => {
                            v_key_3828_ = lean_ctor_get(v___x_3827_, 0);
                            v_val_3829_ = lean_ctor_get(v___x_3827_, 1);
                            lean_inc_ref(v_f_3807_);
                            lean_inc(v___y_3815_);
                            lean_inc_ref(v___y_3814_);
                            lean_inc(v___y_3813_);
                            lean_inc_ref(v___y_3812_);
                            lean_inc(v_val_3829_);
                            lean_inc(v_key_3828_);
                            v___x_3830_ = lean_apply_8(
                                v_f_3807_,
                                v_b_3811_,
                                v_key_3828_,
                                v_val_3829_,
                                v___y_3812_,
                                v___y_3813_,
                                v___y_3814_,
                                v___y_3815_,
                                lean_box(0),
                            );
                            v___y_3823_ = v___x_3830_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_3831_ = lean_ctor_get(v___x_3827_, 0);
                            lean_inc(v_node_3831_);
                            lean_inc_ref(v_f_3807_);
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
                    lean_dec_ref(v_f_3807_);
                    v___x_3833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3833_, 0, v_b_3811_);
                    v___x_3834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3834_, 0, v___x_3833_);
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
                if lean_obj_tag(v___y_3823_) == 0 {
                    v_a_3824_ = lean_ctor_get(v___y_3823_, 0);
                    if lean_obj_tag(v_a_3824_) == 0 {
                        lean_dec_ref(v_f_3807_);
                        return v___y_3823_;
                    } else {
                        lean_inc_ref(v_a_3824_);
                        lean_dec_ref_known(v___y_3823_, 1);
                        v_a_3825_ = lean_ctor_get(v_a_3824_, 0);
                        lean_inc(v_a_3825_);
                        lean_dec_ref_known(v_a_3824_, 1);
                        v_a_3818_ = v_a_3825_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_3807_);
                    return v___y_3823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_f_3835_: *mut LeanObject,
    mut v_as_3836_: *mut LeanObject,
    mut v_i_3837_: *mut LeanObject,
    mut v_stop_3838_: *mut LeanObject,
    mut v_b_3839_: *mut LeanObject,
    mut v___y_3840_: *mut LeanObject,
    mut v___y_3841_: *mut LeanObject,
    mut v___y_3842_: *mut LeanObject,
    mut v___y_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3845_: usize = 0;
    let mut v_stop_boxed_3846_: usize = 0;
    let mut v_res_3847_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3845_ = lean_unbox_usize(v_i_3837_);
    lean_dec(v_i_3837_);
    v_stop_boxed_3846_ = lean_unbox_usize(v_stop_3838_);
    lean_dec(v_stop_3838_);
    v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_3835_, v_as_3836_, v_i_boxed_3845_, v_stop_boxed_3846_, v_b_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
    lean_dec(v___y_3843_);
    lean_dec_ref(v___y_3842_);
    lean_dec(v___y_3841_);
    lean_dec_ref(v___y_3840_);
    lean_dec_ref(v_as_3836_);
    return v_res_3847_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_3848_: *mut LeanObject,
    mut v_x_3849_: *mut LeanObject,
    mut v_x_3850_: *mut LeanObject,
    mut v___y_3851_: *mut LeanObject,
    mut v___y_3852_: *mut LeanObject,
    mut v___y_3853_: *mut LeanObject,
    mut v___y_3854_: *mut LeanObject,
    mut v___y_3855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3856_: *mut LeanObject = core::ptr::null_mut();
    v_res_3856_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_3848_, v_x_3849_, v_x_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
    lean_dec(v___y_3854_);
    lean_dec_ref(v___y_3853_);
    lean_dec(v___y_3852_);
    lean_dec_ref(v___y_3851_);
    return v_res_3856_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(
    mut v_map_3857_: *mut LeanObject,
    mut v_init_3858_: *mut LeanObject,
    mut v_f_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
    mut v___y_3861_: *mut LeanObject,
    mut v___y_3862_: *mut LeanObject,
    mut v___y_3863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v_a_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3875_: u8 = 0;
    let mut v_a_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3865_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                lean_closure_set(v___f_3865_, 0, v_f_3859_);
                lean_inc_ref(v_map_3857_);
                v___x_3866_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v___f_3865_, v_map_3857_, v_init_3858_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
                if lean_obj_tag(v___x_3866_) == 0 {
                    v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3875_ = (!lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3875_ == 0 {
                        v___x_3869_ = v___x_3866_;
                        v_isShared_3870_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3867_);
                        lean_dec(v___x_3866_);
                        v___x_3869_ = lean_box(0);
                        v_isShared_3870_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3876_ = lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3883_ = (!lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3883_ == 0 {
                        v___x_3878_ = v___x_3866_;
                        v_isShared_3879_ = v_isSharedCheck_3883_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3876_);
                        lean_dec(v___x_3866_);
                        v___x_3878_ = lean_box(0);
                        v_isShared_3879_ = v_isSharedCheck_3883_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3871_ = lean_ctor_get(v_a_3867_, 0);
                lean_inc(v_a_3871_);
                lean_dec(v_a_3867_);
                if v_isShared_3870_ == 0 {
                    lean_ctor_set(v___x_3869_, 0, v_a_3871_);
                    v___x_3873_ = v___x_3869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3871_);
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
                    v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
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
    mut v_map_3884_: *mut LeanObject,
    mut v_init_3885_: *mut LeanObject,
    mut v_f_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
    mut v___y_3889_: *mut LeanObject,
    mut v___y_3890_: *mut LeanObject,
    mut v___y_3891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3892_: *mut LeanObject = core::ptr::null_mut();
    v_res_3892_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(v_map_3884_, v_init_3885_, v_f_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
    lean_dec(v___y_3890_);
    lean_dec_ref(v___y_3889_);
    lean_dec(v___y_3888_);
    lean_dec_ref(v___y_3887_);
    lean_dec_ref(v_map_3884_);
    return v_res_3892_;
}
pub unsafe fn l_Lean_Meta_mkDiagSynthPendingFailure(
    mut v_failures_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3917_: u8 = 0;
    let mut v_a_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3921_: u8 = 0;
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3904_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_failures_3898_);
                if v___x_3904_ == 0 {
                    v___x_3905_ = lean_unsigned_to_nat(0);
                    v_data_3906_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__0;
                    v___f_3907_ = l_Lean_Meta_mkDiagSynthPendingFailure___closed__0;
                    v___x_3908_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(v_failures_3898_, v_data_3906_, v___f_3907_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                    if lean_obj_tag(v___x_3908_) == 0 {
                        v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
                        v_isSharedCheck_3917_ = (!lean_is_exclusive(v___x_3908_)) as u8;
                        if v_isSharedCheck_3917_ == 0 {
                            v___x_3911_ = v___x_3908_;
                            v_isShared_3912_ = v_isSharedCheck_3917_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3909_);
                            lean_dec(v___x_3908_);
                            v___x_3911_ = lean_box(0);
                            v_isShared_3912_ = v_isSharedCheck_3917_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3918_ = lean_ctor_get(v___x_3908_, 0);
                        v_isSharedCheck_3925_ = (!lean_is_exclusive(v___x_3908_)) as u8;
                        if v_isSharedCheck_3925_ == 0 {
                            v___x_3920_ = v___x_3908_;
                            v_isShared_3921_ = v_isSharedCheck_3925_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3918_);
                            lean_dec(v___x_3908_);
                            v___x_3920_ = lean_box(0);
                            v_isShared_3921_ = v_isSharedCheck_3925_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3926_ = l_Lean_Meta_instInhabitedDiagSummary_default___closed__1;
                    v___x_3927_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3927_, 0, v___x_3926_);
                    return v___x_3927_;
                }
            }
            1 => {
                v___x_3913_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3913_, 0, v_a_3909_);
                lean_ctor_set(v___x_3913_, 1, v___x_3905_);
                if v_isShared_3912_ == 0 {
                    lean_ctor_set(v___x_3911_, 0, v___x_3913_);
                    v___x_3915_ = v___x_3911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
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
                    v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
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
    mut v_failures_3928_: *mut LeanObject,
    mut v_a_3929_: *mut LeanObject,
    mut v_a_3930_: *mut LeanObject,
    mut v_a_3931_: *mut LeanObject,
    mut v_a_3932_: *mut LeanObject,
    mut v_a_3933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3934_: *mut LeanObject = core::ptr::null_mut();
    v_res_3934_ = l_Lean_Meta_mkDiagSynthPendingFailure(
        v_failures_3928_,
        v_a_3929_,
        v_a_3930_,
        v_a_3931_,
        v_a_3932_,
    );
    lean_dec(v_a_3932_);
    lean_dec_ref(v_a_3931_);
    lean_dec(v_a_3930_);
    lean_dec_ref(v_a_3929_);
    lean_dec_ref(v_failures_3928_);
    return v_res_3934_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1(
    mut v_00_u03c3_3935_: *mut LeanObject,
    mut v_00_u03b2_3936_: *mut LeanObject,
    mut v_map_3937_: *mut LeanObject,
    mut v_init_3938_: *mut LeanObject,
    mut v_f_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
    mut v___y_3941_: *mut LeanObject,
    mut v___y_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___redArg(v_map_3937_, v_init_3938_, v_f_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
    return v___x_3945_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1___boxed(
    mut v_00_u03c3_3946_: *mut LeanObject,
    mut v_00_u03b2_3947_: *mut LeanObject,
    mut v_map_3948_: *mut LeanObject,
    mut v_init_3949_: *mut LeanObject,
    mut v_f_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3954_);
    lean_dec_ref(v___y_3953_);
    lean_dec(v___y_3952_);
    lean_dec_ref(v___y_3951_);
    lean_dec_ref(v_map_3948_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___redArg(
    mut v_map_3957_: *mut LeanObject,
    mut v_f_3958_: *mut LeanObject,
    mut v_init_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
    mut v___y_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    v___x_3965_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_3958_, v_map_3957_, v_init_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
    return v___x_3965_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___redArg___boxed(
    mut v_map_3966_: *mut LeanObject,
    mut v_f_3967_: *mut LeanObject,
    mut v_init_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
    mut v___y_3971_: *mut LeanObject,
    mut v___y_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3974_: *mut LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___redArg(v_map_3966_, v_f_3967_, v_init_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
    lean_dec(v___y_3972_);
    lean_dec_ref(v___y_3971_);
    lean_dec(v___y_3970_);
    lean_dec_ref(v___y_3969_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1(
    mut v_00_u03c3_3975_: *mut LeanObject,
    mut v_00_u03c3_3976_: *mut LeanObject,
    mut v_00_u03b2_3977_: *mut LeanObject,
    mut v_map_3978_: *mut LeanObject,
    mut v_f_3979_: *mut LeanObject,
    mut v_init_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    v___x_3986_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_3979_, v_map_3978_, v_init_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
    return v___x_3986_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1___boxed(
    mut v_00_u03c3_3987_: *mut LeanObject,
    mut v_00_u03c3_3988_: *mut LeanObject,
    mut v_00_u03b2_3989_: *mut LeanObject,
    mut v_map_3990_: *mut LeanObject,
    mut v_f_3991_: *mut LeanObject,
    mut v_init_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3998_: *mut LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1(v_00_u03c3_3987_, v_00_u03c3_3988_, v_00_u03b2_3989_, v_map_3990_, v_f_3991_, v_init_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
    lean_dec(v___y_3996_);
    lean_dec_ref(v___y_3995_);
    lean_dec(v___y_3994_);
    lean_dec_ref(v___y_3993_);
    return v_res_3998_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2(
    mut v_00_u03c3_3999_: *mut LeanObject,
    mut v_00_u03c3_4000_: *mut LeanObject,
    mut v_00_u03b1_4001_: *mut LeanObject,
    mut v_00_u03b2_4002_: *mut LeanObject,
    mut v_f_4003_: *mut LeanObject,
    mut v_x_4004_: *mut LeanObject,
    mut v_x_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    v___x_4011_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___redArg(v_f_4003_, v_x_4004_, v_x_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
    return v___x_4011_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03c3_4012_: *mut LeanObject,
    mut v_00_u03c3_4013_: *mut LeanObject,
    mut v_00_u03b1_4014_: *mut LeanObject,
    mut v_00_u03b2_4015_: *mut LeanObject,
    mut v_f_4016_: *mut LeanObject,
    mut v_x_4017_: *mut LeanObject,
    mut v_x_4018_: *mut LeanObject,
    mut v___y_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4024_: *mut LeanObject = core::ptr::null_mut();
    v_res_4024_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2(v_00_u03c3_4012_, v_00_u03c3_4013_, v_00_u03b1_4014_, v_00_u03b2_4015_, v_f_4016_, v_x_4017_, v_x_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
    lean_dec(v___y_4022_);
    lean_dec_ref(v___y_4021_);
    lean_dec(v___y_4020_);
    lean_dec_ref(v___y_4019_);
    return v_res_4024_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_4025_: *mut LeanObject,
    mut v_00_u03b2_4026_: *mut LeanObject,
    mut v_00_u03c3_4027_: *mut LeanObject,
    mut v_00_u03c3_4028_: *mut LeanObject,
    mut v_f_4029_: *mut LeanObject,
    mut v_as_4030_: *mut LeanObject,
    mut v_i_4031_: usize,
    mut v_stop_4032_: usize,
    mut v_b_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
    mut v___y_4036_: *mut LeanObject,
    mut v___y_4037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4029_, v_as_4030_, v_i_4031_, v_stop_4032_, v_b_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
    return v___x_4039_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_4040_: *mut LeanObject,
    mut v_00_u03b2_4041_: *mut LeanObject,
    mut v_00_u03c3_4042_: *mut LeanObject,
    mut v_00_u03c3_4043_: *mut LeanObject,
    mut v_f_4044_: *mut LeanObject,
    mut v_as_4045_: *mut LeanObject,
    mut v_i_4046_: *mut LeanObject,
    mut v_stop_4047_: *mut LeanObject,
    mut v_b_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
    mut v___y_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4054_: usize = 0;
    let mut v_stop_boxed_4055_: usize = 0;
    let mut v_res_4056_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4054_ = lean_unbox_usize(v_i_4046_);
    lean_dec(v_i_4046_);
    v_stop_boxed_4055_ = lean_unbox_usize(v_stop_4047_);
    lean_dec(v_stop_4047_);
    v_res_4056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4040_, v_00_u03b2_4041_, v_00_u03c3_4042_, v_00_u03c3_4043_, v_f_4044_, v_as_4045_, v_i_boxed_4054_, v_stop_boxed_4055_, v_b_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
    lean_dec(v___y_4052_);
    lean_dec_ref(v___y_4051_);
    lean_dec(v___y_4050_);
    lean_dec_ref(v___y_4049_);
    lean_dec_ref(v_as_4045_);
    return v_res_4056_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03c3_4057_: *mut LeanObject,
    mut v_00_u03c3_4058_: *mut LeanObject,
    mut v_00_u03b1_4059_: *mut LeanObject,
    mut v_00_u03b2_4060_: *mut LeanObject,
    mut v_f_4061_: *mut LeanObject,
    mut v_keys_4062_: *mut LeanObject,
    mut v_vals_4063_: *mut LeanObject,
    mut v_heq_4064_: *mut LeanObject,
    mut v_i_4065_: *mut LeanObject,
    mut v_acc_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
    mut v___y_4069_: *mut LeanObject,
    mut v___y_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    v___x_4072_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4061_, v_keys_4062_, v_vals_4063_, v_i_4065_, v_acc_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
    return v___x_4072_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03c3_4073_: *mut LeanObject,
    mut v_00_u03c3_4074_: *mut LeanObject,
    mut v_00_u03b1_4075_: *mut LeanObject,
    mut v_00_u03b2_4076_: *mut LeanObject,
    mut v_f_4077_: *mut LeanObject,
    mut v_keys_4078_: *mut LeanObject,
    mut v_vals_4079_: *mut LeanObject,
    mut v_heq_4080_: *mut LeanObject,
    mut v_i_4081_: *mut LeanObject,
    mut v_acc_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
    mut v___y_4085_: *mut LeanObject,
    mut v___y_4086_: *mut LeanObject,
    mut v___y_4087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4088_: *mut LeanObject = core::ptr::null_mut();
    v_res_4088_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_mkDiagSynthPendingFailure_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4073_, v_00_u03c3_4074_, v_00_u03b1_4075_, v_00_u03b2_4076_, v_f_4077_, v_keys_4078_, v_vals_4079_, v_heq_4080_, v_i_4081_, v_acc_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
    lean_dec(v___y_4086_);
    lean_dec_ref(v___y_4085_);
    lean_dec(v___y_4084_);
    lean_dec_ref(v___y_4083_);
    lean_dec_ref(v_vals_4079_);
    lean_dec_ref(v_keys_4078_);
    return v_res_4088_;
}
pub unsafe fn l_Lean_Meta_appendSection(
    mut v_m_4092_: *mut LeanObject,
    mut v_cls_4093_: *mut LeanObject,
    mut v_header_4094_: *mut LeanObject,
    mut v_s_4095_: *mut LeanObject,
    mut v_resultSummary_4096_: u8,
) -> *mut LeanObject {
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: u8 = 0;
    let mut v___y_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: f64 = 0.0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_max_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
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
                        v_data_4110_ = lean_ctor_get(v_s_4095_, 0);
                        v_max_4111_ = lean_ctor_get(v_s_4095_, 1);
                        v___x_4112_ = l_Lean_Meta_appendSection___closed__0;
                        v___x_4113_ = lean_string_append(v_header_4094_, v___x_4112_);
                        lean_inc(v_max_4111_);
                        v___x_4114_ = l_Nat_reprFast(v_max_4111_);
                        v___x_4115_ = lean_string_append(v___x_4113_, v___x_4114_);
                        lean_dec_ref(v___x_4114_);
                        v___x_4116_ = l_Lean_Meta_appendSection___closed__1;
                        v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
                        v___x_4118_ = lean_array_get_size(v_data_4110_);
                        v___x_4119_ = l_Nat_reprFast(v___x_4118_);
                        v___x_4120_ = lean_string_append(v___x_4117_, v___x_4119_);
                        lean_dec_ref(v___x_4119_);
                        v___x_4121_ = l_Lean_Meta_appendSection___closed__2;
                        v___x_4122_ = lean_string_append(v___x_4120_, v___x_4121_);
                        v___y_4100_ = v___x_4122_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_s_4095_);
                    lean_dec_ref(v_header_4094_);
                    lean_dec(v_cls_4093_);
                    return v_m_4092_;
                }
            }
            1 => {
                v___x_4101_ = lean_box(0);
                v___x_4102_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0);
                v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
                v___x_4104_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4104_, 0, v_cls_4093_);
                lean_ctor_set(v___x_4104_, 1, v___x_4101_);
                lean_ctor_set(v___x_4104_, 2, v___x_4103_);
                lean_ctor_set_float(
                    v___x_4104_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4102_,
                );
                lean_ctor_set_float(
                    v___x_4104_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4102_,
                );
                lean_ctor_set_uint8(
                    v___x_4104_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4098_,
                );
                v_data_4105_ = lean_ctor_get(v_s_4095_, 0);
                lean_inc_ref(v_data_4105_);
                lean_dec_ref(v_s_4095_);
                v___x_4106_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4106_, 0, v___y_4100_);
                v___x_4107_ = l_Lean_MessageData_ofFormat(v___x_4106_);
                v___x_4108_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4108_, 0, v___x_4104_);
                lean_ctor_set(v___x_4108_, 1, v___x_4107_);
                lean_ctor_set(v___x_4108_, 2, v_data_4105_);
                v___x_4109_ = lean_array_push(v_m_4092_, v___x_4108_);
                return v___x_4109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_appendSection___boxed(
    mut v_m_4123_: *mut LeanObject,
    mut v_cls_4124_: *mut LeanObject,
    mut v_header_4125_: *mut LeanObject,
    mut v_s_4126_: *mut LeanObject,
    mut v_resultSummary_4127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_resultSummary_boxed_4128_: u8 = 0;
    let mut v_res_4129_: *mut LeanObject = core::ptr::null_mut();
    v_resultSummary_boxed_4128_ = (lean_unbox(v_resultSummary_4127_) as u8);
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
    mut v_x_4131_: *mut LeanObject,
) -> u8 {
    return v_a_4130_;
}
pub unsafe fn l_Lean_Meta_reportDiag___lam__0___boxed(
    mut v_a_4132_: *mut LeanObject,
    mut v_x_4133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_13695__boxed_4134_: u8 = 0;
    let mut v_res_4135_: u8 = 0;
    let mut v_r_4136_: *mut LeanObject = core::ptr::null_mut();
    v_a_13695__boxed_4134_ = (lean_unbox(v_a_4132_) as u8);
    v_res_4135_ = l_Lean_Meta_reportDiag___lam__0(v_a_13695__boxed_4134_, v_x_4133_);
    lean_dec(v_x_4133_);
    v_r_4136_ = lean_box((v_res_4135_) as usize);
    return v_r_4136_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0(
    mut v___y_4145_: u8,
    mut v_suppressElabErrors_4146_: u8,
    mut v_x_4147_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4147_) == 1 {
        let mut v_pre_4148_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4148_ = lean_ctor_get(v_x_4147_, 0);
        match lean_obj_tag(v_pre_4148_) {
            1 => {
                let mut v_pre_4149_: *mut LeanObject = core::ptr::null_mut();
                v_pre_4149_ = lean_ctor_get(v_pre_4148_, 0);
                match lean_obj_tag(v_pre_4149_) {
                    0 => {
                        let mut v_str_4150_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_4151_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4153_: u8 = 0;
                        v_str_4150_ = lean_ctor_get(v_x_4147_, 1);
                        v_str_4151_ = lean_ctor_get(v_pre_4148_, 1);
                        v___x_4152_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_4153_ = lean_string_dec_eq(v_str_4151_, v___x_4152_);
                        if v___x_4153_ == 0 {
                            let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4155_: u8 = 0;
                            v___x_4154_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1;
                            v___x_4155_ = lean_string_dec_eq(v_str_4151_, v___x_4154_);
                            if v___x_4155_ == 0 {
                                return v___y_4145_;
                            } else {
                                let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_4160_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_4160_ = lean_ctor_get(v_pre_4149_, 0);
                        if lean_obj_tag(v_pre_4160_) == 0 {
                            let mut v_str_4161_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4162_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4163_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4165_: u8 = 0;
                            v_str_4161_ = lean_ctor_get(v_x_4147_, 1);
                            v_str_4162_ = lean_ctor_get(v_pre_4148_, 1);
                            v_str_4163_ = lean_ctor_get(v_pre_4149_, 1);
                            v___x_4164_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4;
                            v___x_4165_ = lean_string_dec_eq(v_str_4163_, v___x_4164_);
                            if v___x_4165_ == 0 {
                                return v___y_4145_;
                            } else {
                                let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4167_: u8 = 0;
                                v___x_4166_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5;
                                v___x_4167_ = lean_string_dec_eq(v_str_4162_, v___x_4166_);
                                if v___x_4167_ == 0 {
                                    return v___y_4145_;
                                } else {
                                    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_4170_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4172_: u8 = 0;
                v_str_4170_ = lean_ctor_get(v_x_4147_, 1);
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
    mut v___y_4173_: *mut LeanObject,
    mut v_suppressElabErrors_4174_: *mut LeanObject,
    mut v_x_4175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_13717__boxed_4176_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4177_: u8 = 0;
    let mut v_res_4178_: u8 = 0;
    let mut v_r_4179_: *mut LeanObject = core::ptr::null_mut();
    v___y_13717__boxed_4176_ = (lean_unbox(v___y_4173_) as u8);
    v_suppressElabErrors_boxed_4177_ = (lean_unbox(v_suppressElabErrors_4174_) as u8);
    v_res_4178_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0(v___y_13717__boxed_4176_, v_suppressElabErrors_boxed_4177_, v_x_4175_);
    lean_dec(v_x_4175_);
    v_r_4179_ = lean_box((v_res_4178_) as usize);
    return v_r_4179_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1_spec__4(
    mut v_opts_4180_: *mut LeanObject,
    mut v_opt_4181_: *mut LeanObject,
) -> u8 {
    let mut v_name_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    v_name_4182_ = lean_ctor_get(v_opt_4181_, 0);
    v_defValue_4183_ = lean_ctor_get(v_opt_4181_, 1);
    v_map_4184_ = lean_ctor_get(v_opts_4180_, 0);
    v___x_4185_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4184_,
            v_name_4182_,
        );
    if lean_obj_tag(v___x_4185_) == 0 {
        let mut v___x_4186_: u8 = 0;
        v___x_4186_ = (lean_unbox(v_defValue_4183_) as u8);
        return v___x_4186_;
    } else {
        let mut v_val_4187_: *mut LeanObject = core::ptr::null_mut();
        v_val_4187_ = lean_ctor_get(v___x_4185_, 0);
        lean_inc(v_val_4187_);
        lean_dec_ref_known(v___x_4185_, 1);
        if lean_obj_tag(v_val_4187_) == 1 {
            let mut v_v_4188_: u8 = 0;
            v_v_4188_ = lean_ctor_get_uint8(v_val_4187_, 0 as u32);
            lean_dec_ref_known(v_val_4187_, 0);
            return v_v_4188_;
        } else {
            let mut v___x_4189_: u8 = 0;
            lean_dec(v_val_4187_);
            v___x_4189_ = (lean_unbox(v_defValue_4183_) as u8);
            return v___x_4189_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_opts_4190_: *mut LeanObject,
    mut v_opt_4191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4192_: u8 = 0;
    let mut v_r_4193_: *mut LeanObject = core::ptr::null_mut();
    v_res_4192_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1_spec__4(v_opts_4190_, v_opt_4191_);
    lean_dec_ref(v_opt_4191_);
    lean_dec_ref(v_opts_4190_);
    v_r_4193_ = lean_box((v_res_4192_) as usize);
    return v_r_4193_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1(
    mut v_ref_4194_: *mut LeanObject,
    mut v_msgData_4195_: *mut LeanObject,
    mut v_severity_4196_: u8,
    mut v_isSilent_4197_: u8,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4207_: u8 = 0;
    let mut v___y_4208_: u8 = 0;
    let mut v___y_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4227_: u8 = 0;
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v___y_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: u8 = 0;
    let mut v___y_4242_: u8 = 0;
    let mut v___y_4243_: u8 = 0;
    let mut v___y_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut v___y_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: u8 = 0;
    let mut v___y_4267_: u8 = 0;
    let mut v___y_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: u8 = 0;
    let mut v___y_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4278_: u8 = 0;
    let mut v___y_4279_: u8 = 0;
    let mut v___y_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4282_: u8 = 0;
    let mut v_ref_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___y_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4290_: u8 = 0;
    let mut v___y_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4294_: u8 = 0;
    let mut v___y_4295_: u8 = 0;
    let mut v___y_4297_: u8 = 0;
    let mut v_fileName_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4302_: u8 = 0;
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_4195_);
                    v___x_4313_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4195_);
                    v___y_4297_ = v___x_4313_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4213_ = lean_st_ref_take(v___y_4212_);
                v_currNamespace_4214_ = lean_ctor_get(v___y_4211_, 6);
                v_openDecls_4215_ = lean_ctor_get(v___y_4211_, 7);
                v_env_4216_ = lean_ctor_get(v___x_4213_, 0);
                v_nextMacroScope_4217_ = lean_ctor_get(v___x_4213_, 1);
                v_ngen_4218_ = lean_ctor_get(v___x_4213_, 2);
                v_auxDeclNGen_4219_ = lean_ctor_get(v___x_4213_, 3);
                v_traceState_4220_ = lean_ctor_get(v___x_4213_, 4);
                v_cache_4221_ = lean_ctor_get(v___x_4213_, 5);
                v_messages_4222_ = lean_ctor_get(v___x_4213_, 6);
                v_infoState_4223_ = lean_ctor_get(v___x_4213_, 7);
                v_snapshotTasks_4224_ = lean_ctor_get(v___x_4213_, 8);
                v_isSharedCheck_4238_ = (!lean_is_exclusive(v___x_4213_)) as u8;
                if v_isSharedCheck_4238_ == 0 {
                    v___x_4226_ = v___x_4213_;
                    v_isShared_4227_ = v_isSharedCheck_4238_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4224_);
                    lean_inc(v_infoState_4223_);
                    lean_inc(v_messages_4222_);
                    lean_inc(v_cache_4221_);
                    lean_inc(v_traceState_4220_);
                    lean_inc(v_auxDeclNGen_4219_);
                    lean_inc(v_ngen_4218_);
                    lean_inc(v_nextMacroScope_4217_);
                    lean_inc(v_env_4216_);
                    lean_dec(v___x_4213_);
                    v___x_4226_ = lean_box(0);
                    v_isShared_4227_ = v_isSharedCheck_4238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_4215_);
                lean_inc(v_currNamespace_4214_);
                v___x_4228_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4228_, 0, v_currNamespace_4214_);
                lean_ctor_set(v___x_4228_, 1, v_openDecls_4215_);
                v___x_4229_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4229_, 0, v___x_4228_);
                lean_ctor_set(v___x_4229_, 1, v___y_4204_);
                lean_inc_ref(v___y_4206_);
                lean_inc_ref(v___y_4210_);
                v___x_4230_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4230_, 0, v___y_4210_);
                lean_ctor_set(v___x_4230_, 1, v___y_4205_);
                lean_ctor_set(v___x_4230_, 2, v___y_4209_);
                lean_ctor_set(v___x_4230_, 3, v___y_4206_);
                lean_ctor_set(v___x_4230_, 4, v___x_4229_);
                lean_ctor_set_uint8(
                    v___x_4230_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4207_,
                );
                lean_ctor_set_uint8(
                    v___x_4230_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4208_,
                );
                lean_ctor_set_uint8(
                    v___x_4230_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4197_,
                );
                v___x_4231_ = l_Lean_MessageLog_add(v___x_4230_, v_messages_4222_);
                if v_isShared_4227_ == 0 {
                    lean_ctor_set(v___x_4226_, 6, v___x_4231_);
                    v___x_4233_ = v___x_4226_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_env_4216_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_nextMacroScope_4217_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 2, v_ngen_4218_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 3, v_auxDeclNGen_4219_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 4, v_traceState_4220_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 5, v_cache_4221_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 6, v___x_4231_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 7, v_infoState_4223_);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 8, v_snapshotTasks_4224_);
                    v___x_4233_ = v_reuseFailAlloc_4237_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4234_ = lean_st_ref_set(v___y_4212_, v___x_4233_);
                v___x_4235_ = lean_box(0);
                v___x_4236_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4236_, 0, v___x_4235_);
                return v___x_4236_;
            }
            4 => {
                v___x_4248_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4195_,
                    );
                v___x_4249_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkDiagSummary_spec__2_spec__4_spec__7_spec__10_spec__14_spec__16_spec__18_spec__19(v___x_4248_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
                v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
                v_isSharedCheck_4263_ = (!lean_is_exclusive(v___x_4249_)) as u8;
                if v_isSharedCheck_4263_ == 0 {
                    v___x_4252_ = v___x_4249_;
                    v_isShared_4253_ = v_isSharedCheck_4263_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4250_);
                    lean_dec(v___x_4249_);
                    v___x_4252_ = lean_box(0);
                    v_isShared_4253_ = v_isSharedCheck_4263_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_4246_, 2);
                v___x_4254_ = l_Lean_FileMap_toPosition(v___y_4246_, v___y_4244_);
                lean_dec(v___y_4244_);
                v___x_4255_ = l_Lean_FileMap_toPosition(v___y_4246_, v___y_4247_);
                lean_dec(v___y_4247_);
                v___x_4256_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4256_, 0, v___x_4255_);
                v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
                if v___y_4241_ == 0 {
                    lean_del_object(v___x_4252_);
                    lean_dec_ref(v___y_4240_);
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
                    lean_inc(v_a_4250_);
                    v___x_4258_ = l_Lean_MessageData_hasTag(v___y_4240_, v_a_4250_);
                    if v___x_4258_ == 0 {
                        lean_dec_ref_known(v___x_4256_, 1);
                        lean_dec_ref(v___x_4254_);
                        lean_dec(v_a_4250_);
                        v___x_4259_ = lean_box(0);
                        if v_isShared_4253_ == 0 {
                            lean_ctor_set(v___x_4252_, 0, v___x_4259_);
                            v___x_4261_ = v___x_4252_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
                            v___x_4261_ = v_reuseFailAlloc_4262_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4252_);
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
                lean_dec(v___y_4268_);
                if lean_obj_tag(v___x_4273_) == 0 {
                    lean_inc(v___y_4272_);
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
                    v_val_4274_ = lean_ctor_get(v___x_4273_, 0);
                    lean_inc(v_val_4274_);
                    lean_dec_ref_known(v___x_4273_, 1);
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
                if lean_obj_tag(v___x_4284_) == 0 {
                    v___x_4285_ = lean_unsigned_to_nat(0);
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
                    v_val_4286_ = lean_ctor_get(v___x_4284_, 0);
                    lean_inc(v_val_4286_);
                    lean_dec_ref_known(v___x_4284_, 1);
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
                    v_fileName_4298_ = lean_ctor_get(v___y_4200_, 0);
                    v_fileMap_4299_ = lean_ctor_get(v___y_4200_, 1);
                    v_options_4300_ = lean_ctor_get(v___y_4200_, 2);
                    v_ref_4301_ = lean_ctor_get(v___y_4200_, 5);
                    v_suppressElabErrors_4302_ = lean_ctor_get_uint8(
                        v___y_4200_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4303_ = lean_box((v___y_4297_) as usize);
                    v___x_4304_ = lean_box((v_suppressElabErrors_4302_) as usize);
                    v___f_4305_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4305_, 0, v___x_4303_);
                    lean_closure_set(v___f_4305_, 1, v___x_4304_);
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
                    lean_dec_ref(v_msgData_4195_);
                    v___x_4310_ = lean_box(0);
                    v___x_4311_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4311_, 0, v___x_4310_);
                    return v___x_4311_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1___boxed(
    mut v_ref_4314_: *mut LeanObject,
    mut v_msgData_4315_: *mut LeanObject,
    mut v_severity_4316_: *mut LeanObject,
    mut v_isSilent_4317_: *mut LeanObject,
    mut v___y_4318_: *mut LeanObject,
    mut v___y_4319_: *mut LeanObject,
    mut v___y_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4323_: u8 = 0;
    let mut v_isSilent_boxed_4324_: u8 = 0;
    let mut v_res_4325_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4323_ = (lean_unbox(v_severity_4316_) as u8);
    v_isSilent_boxed_4324_ = (lean_unbox(v_isSilent_4317_) as u8);
    v_res_4325_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1(v_ref_4314_, v_msgData_4315_, v_severity_boxed_4323_, v_isSilent_boxed_4324_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
    lean_dec(v___y_4321_);
    lean_dec_ref(v___y_4320_);
    lean_dec(v___y_4319_);
    lean_dec_ref(v___y_4318_);
    lean_dec(v_ref_4314_);
    return v_res_4325_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0(
    mut v_msgData_4326_: *mut LeanObject,
    mut v_severity_4327_: u8,
    mut v_isSilent_4328_: u8,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4334_ = lean_ctor_get(v___y_4331_, 5);
    v___x_4335_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0_spec__1(v_ref_4334_, v_msgData_4326_, v_severity_4327_, v_isSilent_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
    return v___x_4335_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0___boxed(
    mut v_msgData_4336_: *mut LeanObject,
    mut v_severity_4337_: *mut LeanObject,
    mut v_isSilent_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4344_: u8 = 0;
    let mut v_isSilent_boxed_4345_: u8 = 0;
    let mut v_res_4346_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4344_ = (lean_unbox(v_severity_4337_) as u8);
    v_isSilent_boxed_4345_ = (lean_unbox(v_isSilent_4338_) as u8);
    v_res_4346_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0_spec__0(
        v_msgData_4336_,
        v_severity_boxed_4344_,
        v_isSilent_boxed_4345_,
        v___y_4339_,
        v___y_4340_,
        v___y_4341_,
        v___y_4342_,
    );
    lean_dec(v___y_4342_);
    lean_dec_ref(v___y_4341_);
    lean_dec(v___y_4340_);
    lean_dec_ref(v___y_4339_);
    return v_res_4346_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0(
    mut v_msgData_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_msgData_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
    mut v___y_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4362_: *mut LeanObject = core::ptr::null_mut();
    v_res_4362_ = l_Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0(
        v_msgData_4356_,
        v___y_4357_,
        v___y_4358_,
        v___y_4359_,
        v___y_4360_,
    );
    lean_dec(v___y_4360_);
    lean_dec_ref(v___y_4359_);
    lean_dec(v___y_4358_);
    lean_dec_ref(v___y_4357_);
    return v_res_4362_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__0() -> *mut LeanObject {
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    v___x_4363_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4363_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    v___x_4364_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__0_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__0,
    );
    v___x_4365_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4365_, 0, v___x_4364_);
    return v___x_4365_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__2() -> *mut LeanObject {
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    v___x_4366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4367_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4367_, 0, v___x_4366_);
    lean_ctor_set(v___x_4367_, 1, v___x_4366_);
    lean_ctor_set(v___x_4367_, 2, v___x_4366_);
    lean_ctor_set(v___x_4367_, 3, v___x_4366_);
    lean_ctor_set(v___x_4367_, 4, v___x_4366_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    v___x_4368_ = 0;
    v___x_4369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4370_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_4370_, 0, v___x_4369_);
    lean_ctor_set_uint8(
        v___x_4370_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4368_,
    );
    return v___x_4370_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    v___x_4371_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4372_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4372_, 0, v___x_4371_);
    lean_ctor_set(v___x_4372_, 1, v___x_4371_);
    return v___x_4372_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__5() -> *mut LeanObject {
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    v___x_4373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__1_once),
        _init_l_Lean_Meta_reportDiag___lam__1___closed__1,
    );
    v___x_4374_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4374_, 0, v___x_4373_);
    lean_ctor_set(v___x_4374_, 1, v___x_4373_);
    lean_ctor_set(v___x_4374_, 2, v___x_4373_);
    lean_ctor_set(v___x_4374_, 3, v___x_4373_);
    lean_ctor_set(v___x_4374_, 4, v___x_4373_);
    lean_ctor_set(v___x_4374_, 5, v___x_4373_);
    return v___x_4374_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__20() -> *mut LeanObject {
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    v___x_4392_ = l_Lean_Meta_reportDiag___lam__1___closed__19;
    v___x_4393_ = l_Lean_MessageData_ofFormat(v___x_4392_);
    return v___x_4393_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__23() -> *mut LeanObject {
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: u8 = 0;
    let mut v___x_4399_: f64 = 0.0;
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    v___x_4397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__1;
    v___x_4398_ = 0;
    v___x_4399_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkDiagSummary_spec__3___closed__0);
    v___x_4400_ = lean_box(0);
    v___x_4401_ = l_Lean_Meta_reportDiag___lam__1___closed__22;
    v___x_4402_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_4402_, 0, v___x_4401_);
    lean_ctor_set(v___x_4402_, 1, v___x_4400_);
    lean_ctor_set(v___x_4402_, 2, v___x_4397_);
    lean_ctor_set_float(
        v___x_4402_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4399_,
    );
    lean_ctor_set_float(
        v___x_4402_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_4399_,
    );
    lean_ctor_set_uint8(
        v___x_4402_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_4398_,
    );
    return v___x_4402_;
}
pub unsafe fn _init_l_Lean_Meta_reportDiag___lam__1___closed__26() -> *mut LeanObject {
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    v___x_4406_ = l_Lean_Meta_reportDiag___lam__1___closed__25;
    v___x_4407_ = l_Lean_MessageData_ofFormat(v___x_4406_);
    return v___x_4407_;
}
pub unsafe fn l_Lean_Meta_reportDiag___lam__1(
    mut v_a_4408_: u8,
    mut v___f_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
    mut v___y_4412_: *mut LeanObject,
    mut v___y_4413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: u8 = 0;
    let mut v___y_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4429_: u8 = 0;
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4445_: u8 = 0;
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4459_: u8 = 0;
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_unused_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_unused_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut v_unused_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldAxiomCounter_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_heuristicCounter_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingFailures_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v_a_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut v_a_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_a_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4567_: u8 = 0;
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_a_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4575_: u8 = 0;
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut v_a_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut v_a_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut v_a_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4415_ = lean_st_ref_get(v___y_4411_);
                v_diag_4416_ = lean_ctor_get(v___x_4415_, 4);
                lean_inc_ref(v_diag_4416_);
                lean_dec(v___x_4415_);
                v_unfoldCounter_4417_ = lean_ctor_get(v_diag_4416_, 0);
                lean_inc_ref(v_unfoldCounter_4417_);
                lean_dec_ref(v_diag_4416_);
                v___x_4418_ = 0;
                v___x_4475_ = l_Lean_Meta_mkDiagSummaryForUnfolded(
                    v_unfoldCounter_4417_,
                    v___x_4418_,
                    v___y_4410_,
                    v___y_4411_,
                    v___y_4412_,
                    v___y_4413_,
                );
                if lean_obj_tag(v___x_4475_) == 0 {
                    v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
                    lean_inc(v_a_4476_);
                    lean_dec_ref_known(v___x_4475_, 1);
                    v___x_4477_ = l_Lean_Meta_mkDiagSummaryForUnfolded(
                        v_unfoldCounter_4417_,
                        v_a_4408_,
                        v___y_4410_,
                        v___y_4411_,
                        v___y_4412_,
                        v___y_4413_,
                    );
                    if lean_obj_tag(v___x_4477_) == 0 {
                        v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
                        lean_inc(v_a_4478_);
                        lean_dec_ref_known(v___x_4477_, 1);
                        v___x_4479_ = lean_st_ref_get(v___y_4411_);
                        v_diag_4480_ = lean_ctor_get(v___x_4479_, 4);
                        lean_inc_ref(v_diag_4480_);
                        lean_dec(v___x_4479_);
                        v_unfoldAxiomCounter_4481_ = lean_ctor_get(v_diag_4480_, 1);
                        lean_inc_ref(v_unfoldAxiomCounter_4481_);
                        lean_dec_ref(v_diag_4480_);
                        v___x_4482_ = l_Lean_Meta_mkDiagSummaryForUnfolded___closed__1;
                        lean_inc_ref(v___f_4409_);
                        v___x_4483_ = l_Lean_Meta_mkDiagSummary(
                            v___x_4482_,
                            v_unfoldAxiomCounter_4481_,
                            v___f_4409_,
                            v___y_4410_,
                            v___y_4411_,
                            v___y_4412_,
                            v___y_4413_,
                        );
                        lean_dec_ref(v_unfoldAxiomCounter_4481_);
                        if lean_obj_tag(v___x_4483_) == 0 {
                            v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
                            lean_inc(v_a_4484_);
                            lean_dec_ref_known(v___x_4483_, 1);
                            v___x_4485_ = l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(
                                v_unfoldCounter_4417_,
                                v___y_4410_,
                                v___y_4411_,
                                v___y_4412_,
                                v___y_4413_,
                            );
                            lean_dec_ref(v_unfoldCounter_4417_);
                            if lean_obj_tag(v___x_4485_) == 0 {
                                v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
                                lean_inc(v_a_4486_);
                                lean_dec_ref_known(v___x_4485_, 1);
                                v___x_4487_ = lean_st_ref_get(v___y_4411_);
                                v_diag_4488_ = lean_ctor_get(v___x_4487_, 4);
                                lean_inc_ref(v_diag_4488_);
                                lean_dec(v___x_4487_);
                                v_heuristicCounter_4489_ = lean_ctor_get(v_diag_4488_, 2);
                                lean_inc_ref(v_heuristicCounter_4489_);
                                lean_dec_ref(v_diag_4488_);
                                v___x_4490_ = l_Lean_Meta_reportDiag___lam__1___closed__7;
                                lean_inc_ref(v___f_4409_);
                                v___x_4491_ = l_Lean_Meta_mkDiagSummary(
                                    v___x_4490_,
                                    v_heuristicCounter_4489_,
                                    v___f_4409_,
                                    v___y_4410_,
                                    v___y_4411_,
                                    v___y_4412_,
                                    v___y_4413_,
                                );
                                lean_dec_ref(v_heuristicCounter_4489_);
                                if lean_obj_tag(v___x_4491_) == 0 {
                                    v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
                                    lean_inc(v_a_4492_);
                                    lean_dec_ref_known(v___x_4491_, 1);
                                    v___x_4493_ = l_Lean_Meta_mkDiagSummaryForUsedInstances(
                                        v___y_4410_,
                                        v___y_4411_,
                                        v___y_4412_,
                                        v___y_4413_,
                                    );
                                    if lean_obj_tag(v___x_4493_) == 0 {
                                        v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
                                        lean_inc(v_a_4494_);
                                        lean_dec_ref_known(v___x_4493_, 1);
                                        v___x_4495_ = lean_st_ref_get(v___y_4411_);
                                        v_diag_4496_ = lean_ctor_get(v___x_4495_, 4);
                                        lean_inc_ref(v_diag_4496_);
                                        lean_dec(v___x_4495_);
                                        v_synthPendingFailures_4497_ =
                                            lean_ctor_get(v_diag_4496_, 4);
                                        lean_inc_ref(v_synthPendingFailures_4497_);
                                        lean_dec_ref(v_diag_4496_);
                                        v___x_4498_ = l_Lean_Meta_mkDiagSynthPendingFailure(
                                            v_synthPendingFailures_4497_,
                                            v___y_4410_,
                                            v___y_4411_,
                                            v___y_4412_,
                                            v___y_4413_,
                                        );
                                        lean_dec_ref(v_synthPendingFailures_4497_);
                                        if lean_obj_tag(v___x_4498_) == 0 {
                                            v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
                                            lean_inc(v_a_4499_);
                                            lean_dec_ref_known(v___x_4498_, 1);
                                            v___x_4500_ = lean_st_ref_get(v___y_4413_);
                                            v_env_4501_ = lean_ctor_get(v___x_4500_, 0);
                                            lean_inc_ref(v_env_4501_);
                                            lean_dec(v___x_4500_);
                                            v___x_4502_ = l_Lean_Kernel_getDiagnostics(v_env_4501_);
                                            v_unfoldCounter_4503_ = lean_ctor_get(v___x_4502_, 0);
                                            lean_inc_ref(v_unfoldCounter_4503_);
                                            lean_dec_ref(v___x_4502_);
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
                                            lean_dec_ref(v_unfoldCounter_4503_);
                                            if lean_obj_tag(v___x_4505_) == 0 {
                                                v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
                                                lean_inc(v_a_4506_);
                                                lean_dec_ref_known(v___x_4505_, 1);
                                                v___x_4507_ = lean_unsigned_to_nat(0);
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
                                                v_options_4511_ = lean_ctor_get(v___y_4412_, 2);
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
                                                lean_dec_ref(v___x_4522_);
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
                                                    v___x_4534_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__20), core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__20_once), _init_l_Lean_Meta_reportDiag___lam__1___closed__20);
                                                    v___x_4535_ =
                                                        lean_array_push(v___x_4531_, v___x_4534_);
                                                    v___x_4536_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__23), core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__23_once), _init_l_Lean_Meta_reportDiag___lam__1___closed__23);
                                                    v___x_4537_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__26), core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__26_once), _init_l_Lean_Meta_reportDiag___lam__1___closed__26);
                                                    v___x_4538_ = lean_alloc_ctor(9, 3, (0) as u32);
                                                    lean_ctor_set(v___x_4538_, 0, v___x_4536_);
                                                    lean_ctor_set(v___x_4538_, 1, v___x_4537_);
                                                    lean_ctor_set(v___x_4538_, 2, v___x_4535_);
                                                    v___x_4539_ = l_Lean_logInfo___at___00Lean_Meta_reportDiag_spec__0(v___x_4538_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
                                                    if lean_obj_tag(v___x_4539_) == 0 {
                                                        lean_dec_ref_known(v___x_4539_, 1);
                                                        v___y_4420_ = v___y_4411_;
                                                        v___y_4421_ = v___y_4413_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        return v___x_4539_;
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_4531_);
                                                    v___y_4420_ = v___y_4411_;
                                                    v___y_4421_ = v___y_4413_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_a_4499_);
                                                lean_dec(v_a_4494_);
                                                lean_dec(v_a_4492_);
                                                lean_dec(v_a_4486_);
                                                lean_dec(v_a_4484_);
                                                lean_dec(v_a_4478_);
                                                lean_dec(v_a_4476_);
                                                v_a_4540_ = lean_ctor_get(v___x_4505_, 0);
                                                v_isSharedCheck_4547_ =
                                                    (!lean_is_exclusive(v___x_4505_)) as u8;
                                                if v_isSharedCheck_4547_ == 0 {
                                                    v___x_4542_ = v___x_4505_;
                                                    v_isShared_4543_ = v_isSharedCheck_4547_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4540_);
                                                    lean_dec(v___x_4505_);
                                                    v___x_4542_ = lean_box(0);
                                                    v_isShared_4543_ = v_isSharedCheck_4547_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_4494_);
                                            lean_dec(v_a_4492_);
                                            lean_dec(v_a_4486_);
                                            lean_dec(v_a_4484_);
                                            lean_dec(v_a_4478_);
                                            lean_dec(v_a_4476_);
                                            lean_dec_ref(v___f_4409_);
                                            v_a_4548_ = lean_ctor_get(v___x_4498_, 0);
                                            v_isSharedCheck_4555_ =
                                                (!lean_is_exclusive(v___x_4498_)) as u8;
                                            if v_isSharedCheck_4555_ == 0 {
                                                v___x_4550_ = v___x_4498_;
                                                v_isShared_4551_ = v_isSharedCheck_4555_;
                                                state = 10;
                                                continue;
                                            } else {
                                                lean_inc(v_a_4548_);
                                                lean_dec(v___x_4498_);
                                                v___x_4550_ = lean_box(0);
                                                v_isShared_4551_ = v_isSharedCheck_4555_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_4492_);
                                        lean_dec(v_a_4486_);
                                        lean_dec(v_a_4484_);
                                        lean_dec(v_a_4478_);
                                        lean_dec(v_a_4476_);
                                        lean_dec_ref(v___f_4409_);
                                        v_a_4556_ = lean_ctor_get(v___x_4493_, 0);
                                        v_isSharedCheck_4563_ =
                                            (!lean_is_exclusive(v___x_4493_)) as u8;
                                        if v_isSharedCheck_4563_ == 0 {
                                            v___x_4558_ = v___x_4493_;
                                            v_isShared_4559_ = v_isSharedCheck_4563_;
                                            state = 12;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4556_);
                                            lean_dec(v___x_4493_);
                                            v___x_4558_ = lean_box(0);
                                            v_isShared_4559_ = v_isSharedCheck_4563_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_4486_);
                                    lean_dec(v_a_4484_);
                                    lean_dec(v_a_4478_);
                                    lean_dec(v_a_4476_);
                                    lean_dec_ref(v___f_4409_);
                                    v_a_4564_ = lean_ctor_get(v___x_4491_, 0);
                                    v_isSharedCheck_4571_ = (!lean_is_exclusive(v___x_4491_)) as u8;
                                    if v_isSharedCheck_4571_ == 0 {
                                        v___x_4566_ = v___x_4491_;
                                        v_isShared_4567_ = v_isSharedCheck_4571_;
                                        state = 14;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4564_);
                                        lean_dec(v___x_4491_);
                                        v___x_4566_ = lean_box(0);
                                        v_isShared_4567_ = v_isSharedCheck_4571_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4484_);
                                lean_dec(v_a_4478_);
                                lean_dec(v_a_4476_);
                                lean_dec_ref(v___f_4409_);
                                v_a_4572_ = lean_ctor_get(v___x_4485_, 0);
                                v_isSharedCheck_4579_ = (!lean_is_exclusive(v___x_4485_)) as u8;
                                if v_isSharedCheck_4579_ == 0 {
                                    v___x_4574_ = v___x_4485_;
                                    v_isShared_4575_ = v_isSharedCheck_4579_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_4572_);
                                    lean_dec(v___x_4485_);
                                    v___x_4574_ = lean_box(0);
                                    v_isShared_4575_ = v_isSharedCheck_4579_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4478_);
                            lean_dec(v_a_4476_);
                            lean_dec_ref(v_unfoldCounter_4417_);
                            lean_dec_ref(v___f_4409_);
                            v_a_4580_ = lean_ctor_get(v___x_4483_, 0);
                            v_isSharedCheck_4587_ = (!lean_is_exclusive(v___x_4483_)) as u8;
                            if v_isSharedCheck_4587_ == 0 {
                                v___x_4582_ = v___x_4483_;
                                v_isShared_4583_ = v_isSharedCheck_4587_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4580_);
                                lean_dec(v___x_4483_);
                                v___x_4582_ = lean_box(0);
                                v_isShared_4583_ = v_isSharedCheck_4587_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4476_);
                        lean_dec_ref(v_unfoldCounter_4417_);
                        lean_dec_ref(v___f_4409_);
                        v_a_4588_ = lean_ctor_get(v___x_4477_, 0);
                        v_isSharedCheck_4595_ = (!lean_is_exclusive(v___x_4477_)) as u8;
                        if v_isSharedCheck_4595_ == 0 {
                            v___x_4590_ = v___x_4477_;
                            v_isShared_4591_ = v_isSharedCheck_4595_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_4588_);
                            lean_dec(v___x_4477_);
                            v___x_4590_ = lean_box(0);
                            v_isShared_4591_ = v_isSharedCheck_4595_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_unfoldCounter_4417_);
                    lean_dec_ref(v___f_4409_);
                    v_a_4596_ = lean_ctor_get(v___x_4475_, 0);
                    v_isSharedCheck_4603_ = (!lean_is_exclusive(v___x_4475_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4598_ = v___x_4475_;
                        v_isShared_4599_ = v_isSharedCheck_4603_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_4596_);
                        lean_dec(v___x_4475_);
                        v___x_4598_ = lean_box(0);
                        v_isShared_4599_ = v_isSharedCheck_4603_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4422_ = lean_st_ref_take(v___y_4420_);
                v_mctx_4423_ = lean_ctor_get(v___x_4422_, 0);
                v_cache_4424_ = lean_ctor_get(v___x_4422_, 1);
                v_zetaDeltaFVarIds_4425_ = lean_ctor_get(v___x_4422_, 2);
                v_postponed_4426_ = lean_ctor_get(v___x_4422_, 3);
                v_isSharedCheck_4473_ = (!lean_is_exclusive(v___x_4422_)) as u8;
                if v_isSharedCheck_4473_ == 0 {
                    v_unused_4474_ = lean_ctor_get(v___x_4422_, 4);
                    lean_dec(v_unused_4474_);
                    v___x_4428_ = v___x_4422_;
                    v_isShared_4429_ = v_isSharedCheck_4473_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_postponed_4426_);
                    lean_inc(v_zetaDeltaFVarIds_4425_);
                    lean_inc(v_cache_4424_);
                    lean_inc(v_mctx_4423_);
                    lean_dec(v___x_4422_);
                    v___x_4428_ = lean_box(0);
                    v_isShared_4429_ = v_isSharedCheck_4473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4430_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__2_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__2,
                );
                if v_isShared_4429_ == 0 {
                    lean_ctor_set(v___x_4428_, 4, v___x_4430_);
                    v___x_4432_ = v___x_4428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_mctx_4423_);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_cache_4424_);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 2, v_zetaDeltaFVarIds_4425_);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 3, v_postponed_4426_);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 4, v___x_4430_);
                    v___x_4432_ = v_reuseFailAlloc_4472_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4433_ = lean_st_ref_set(v___y_4420_, v___x_4432_);
                v___x_4434_ = lean_st_ref_take(v___y_4421_);
                v_env_4435_ = lean_ctor_get(v___x_4434_, 0);
                v_nextMacroScope_4436_ = lean_ctor_get(v___x_4434_, 1);
                v_ngen_4437_ = lean_ctor_get(v___x_4434_, 2);
                v_auxDeclNGen_4438_ = lean_ctor_get(v___x_4434_, 3);
                v_traceState_4439_ = lean_ctor_get(v___x_4434_, 4);
                v_messages_4440_ = lean_ctor_get(v___x_4434_, 6);
                v_infoState_4441_ = lean_ctor_get(v___x_4434_, 7);
                v_snapshotTasks_4442_ = lean_ctor_get(v___x_4434_, 8);
                v_isSharedCheck_4470_ = (!lean_is_exclusive(v___x_4434_)) as u8;
                if v_isSharedCheck_4470_ == 0 {
                    v_unused_4471_ = lean_ctor_get(v___x_4434_, 5);
                    lean_dec(v_unused_4471_);
                    v___x_4444_ = v___x_4434_;
                    v_isShared_4445_ = v_isSharedCheck_4470_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4442_);
                    lean_inc(v_infoState_4441_);
                    lean_inc(v_messages_4440_);
                    lean_inc(v_traceState_4439_);
                    lean_inc(v_auxDeclNGen_4438_);
                    lean_inc(v_ngen_4437_);
                    lean_inc(v_nextMacroScope_4436_);
                    lean_inc(v_env_4435_);
                    lean_dec(v___x_4434_);
                    v___x_4444_ = lean_box(0);
                    v_isShared_4445_ = v_isSharedCheck_4470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4446_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__3_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__3,
                );
                v___x_4447_ = l_Lean_Kernel_setDiagnostics(v_env_4435_, v___x_4446_);
                v___x_4448_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__4_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__4,
                );
                if v_isShared_4445_ == 0 {
                    lean_ctor_set(v___x_4444_, 5, v___x_4448_);
                    lean_ctor_set(v___x_4444_, 0, v___x_4447_);
                    v___x_4450_ = v___x_4444_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4447_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 1, v_nextMacroScope_4436_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 2, v_ngen_4437_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 3, v_auxDeclNGen_4438_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 4, v_traceState_4439_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 5, v___x_4448_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 6, v_messages_4440_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 7, v_infoState_4441_);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 8, v_snapshotTasks_4442_);
                    v___x_4450_ = v_reuseFailAlloc_4469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4451_ = lean_st_ref_set(v___y_4421_, v___x_4450_);
                v___x_4452_ = lean_st_ref_take(v___y_4420_);
                v_mctx_4453_ = lean_ctor_get(v___x_4452_, 0);
                v_zetaDeltaFVarIds_4454_ = lean_ctor_get(v___x_4452_, 2);
                v_postponed_4455_ = lean_ctor_get(v___x_4452_, 3);
                v_diag_4456_ = lean_ctor_get(v___x_4452_, 4);
                v_isSharedCheck_4467_ = (!lean_is_exclusive(v___x_4452_)) as u8;
                if v_isSharedCheck_4467_ == 0 {
                    v_unused_4468_ = lean_ctor_get(v___x_4452_, 1);
                    lean_dec(v_unused_4468_);
                    v___x_4458_ = v___x_4452_;
                    v_isShared_4459_ = v_isSharedCheck_4467_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_diag_4456_);
                    lean_inc(v_postponed_4455_);
                    lean_inc(v_zetaDeltaFVarIds_4454_);
                    lean_inc(v_mctx_4453_);
                    lean_dec(v___x_4452_);
                    v___x_4458_ = lean_box(0);
                    v_isShared_4459_ = v_isSharedCheck_4467_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4460_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reportDiag___lam__1___closed__5_once),
                    _init_l_Lean_Meta_reportDiag___lam__1___closed__5,
                );
                if v_isShared_4459_ == 0 {
                    lean_ctor_set(v___x_4458_, 1, v___x_4460_);
                    v___x_4462_ = v___x_4458_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_mctx_4453_);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 1, v___x_4460_);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 2, v_zetaDeltaFVarIds_4454_);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 3, v_postponed_4455_);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 4, v_diag_4456_);
                    v___x_4462_ = v_reuseFailAlloc_4466_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4463_ = lean_st_ref_set(v___y_4420_, v___x_4462_);
                v___x_4464_ = lean_box(0);
                v___x_4465_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4465_, 0, v___x_4464_);
                return v___x_4465_;
            }
            8 => {
                if v_isShared_4543_ == 0 {
                    v___x_4545_ = v___x_4542_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
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
                    v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
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
                    v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
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
                    v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
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
                    v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
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
                    v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
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
                    v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
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
                    v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
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
    mut v_a_4604_: *mut LeanObject,
    mut v___f_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
    mut v___y_4607_: *mut LeanObject,
    mut v___y_4608_: *mut LeanObject,
    mut v___y_4609_: *mut LeanObject,
    mut v___y_4610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_14165__boxed_4611_: u8 = 0;
    let mut v_res_4612_: *mut LeanObject = core::ptr::null_mut();
    v_a_14165__boxed_4611_ = (lean_unbox(v_a_4604_) as u8);
    v_res_4612_ = l_Lean_Meta_reportDiag___lam__1(
        v_a_14165__boxed_4611_,
        v___f_4605_,
        v___y_4606_,
        v___y_4607_,
        v___y_4608_,
        v___y_4609_,
    );
    lean_dec(v___y_4609_);
    lean_dec_ref(v___y_4608_);
    lean_dec(v___y_4607_);
    lean_dec_ref(v___y_4606_);
    return v_res_4612_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(
    mut v___y_4613_: *mut LeanObject,
    mut v_isExporting_4614_: u8,
    mut v___x_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___x_4617_: *mut LeanObject,
    mut v_a_x3f_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4650_: u8 = 0;
    let mut v_unused_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4653_: u8 = 0;
    let mut v_unused_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4620_ = lean_st_ref_take(v___y_4613_);
                v_env_4621_ = lean_ctor_get(v___x_4620_, 0);
                v_nextMacroScope_4622_ = lean_ctor_get(v___x_4620_, 1);
                v_ngen_4623_ = lean_ctor_get(v___x_4620_, 2);
                v_auxDeclNGen_4624_ = lean_ctor_get(v___x_4620_, 3);
                v_traceState_4625_ = lean_ctor_get(v___x_4620_, 4);
                v_messages_4626_ = lean_ctor_get(v___x_4620_, 6);
                v_infoState_4627_ = lean_ctor_get(v___x_4620_, 7);
                v_snapshotTasks_4628_ = lean_ctor_get(v___x_4620_, 8);
                v_isSharedCheck_4653_ = (!lean_is_exclusive(v___x_4620_)) as u8;
                if v_isSharedCheck_4653_ == 0 {
                    v_unused_4654_ = lean_ctor_get(v___x_4620_, 5);
                    lean_dec(v_unused_4654_);
                    v___x_4630_ = v___x_4620_;
                    v_isShared_4631_ = v_isSharedCheck_4653_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4628_);
                    lean_inc(v_infoState_4627_);
                    lean_inc(v_messages_4626_);
                    lean_inc(v_traceState_4625_);
                    lean_inc(v_auxDeclNGen_4624_);
                    lean_inc(v_ngen_4623_);
                    lean_inc(v_nextMacroScope_4622_);
                    lean_inc(v_env_4621_);
                    lean_dec(v___x_4620_);
                    v___x_4630_ = lean_box(0);
                    v_isShared_4631_ = v_isSharedCheck_4653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4632_ = l_Lean_Environment_setExporting(v_env_4621_, v_isExporting_4614_);
                if v_isShared_4631_ == 0 {
                    lean_ctor_set(v___x_4630_, 5, v___x_4615_);
                    lean_ctor_set(v___x_4630_, 0, v___x_4632_);
                    v___x_4634_ = v___x_4630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4632_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 1, v_nextMacroScope_4622_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 2, v_ngen_4623_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 3, v_auxDeclNGen_4624_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 4, v_traceState_4625_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 5, v___x_4615_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 6, v_messages_4626_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 7, v_infoState_4627_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 8, v_snapshotTasks_4628_);
                    v___x_4634_ = v_reuseFailAlloc_4652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4635_ = lean_st_ref_set(v___y_4613_, v___x_4634_);
                v___x_4636_ = lean_st_ref_take(v___y_4616_);
                v_mctx_4637_ = lean_ctor_get(v___x_4636_, 0);
                v_zetaDeltaFVarIds_4638_ = lean_ctor_get(v___x_4636_, 2);
                v_postponed_4639_ = lean_ctor_get(v___x_4636_, 3);
                v_diag_4640_ = lean_ctor_get(v___x_4636_, 4);
                v_isSharedCheck_4650_ = (!lean_is_exclusive(v___x_4636_)) as u8;
                if v_isSharedCheck_4650_ == 0 {
                    v_unused_4651_ = lean_ctor_get(v___x_4636_, 1);
                    lean_dec(v_unused_4651_);
                    v___x_4642_ = v___x_4636_;
                    v_isShared_4643_ = v_isSharedCheck_4650_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_4640_);
                    lean_inc(v_postponed_4639_);
                    lean_inc(v_zetaDeltaFVarIds_4638_);
                    lean_inc(v_mctx_4637_);
                    lean_dec(v___x_4636_);
                    v___x_4642_ = lean_box(0);
                    v_isShared_4643_ = v_isSharedCheck_4650_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4643_ == 0 {
                    lean_ctor_set(v___x_4642_, 1, v___x_4617_);
                    v___x_4645_ = v___x_4642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_mctx_4637_);
                    lean_ctor_set(v_reuseFailAlloc_4649_, 1, v___x_4617_);
                    lean_ctor_set(v_reuseFailAlloc_4649_, 2, v_zetaDeltaFVarIds_4638_);
                    lean_ctor_set(v_reuseFailAlloc_4649_, 3, v_postponed_4639_);
                    lean_ctor_set(v_reuseFailAlloc_4649_, 4, v_diag_4640_);
                    v___x_4645_ = v_reuseFailAlloc_4649_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4646_ = lean_st_ref_set(v___y_4616_, v___x_4645_);
                v___x_4647_ = lean_box(0);
                v___x_4648_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4648_, 0, v___x_4647_);
                return v___x_4648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0___boxed(
    mut v___y_4655_: *mut LeanObject,
    mut v_isExporting_4656_: *mut LeanObject,
    mut v___x_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
    mut v___x_4659_: *mut LeanObject,
    mut v_a_x3f_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4662_: u8 = 0;
    let mut v_res_4663_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4662_ = (lean_unbox(v_isExporting_4656_) as u8);
    v_res_4663_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_4655_, v_isExporting_boxed_4662_, v___x_4657_, v___y_4658_, v___x_4659_, v_a_x3f_4660_);
    lean_dec(v_a_x3f_4660_);
    lean_dec(v___y_4658_);
    lean_dec(v___y_4655_);
    return v_res_4663_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    v___x_4664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4664_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    v___x_4665_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__0);
    v___x_4666_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4666_, 0, v___x_4665_);
    return v___x_4666_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1);
    v___x_4668_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4668_, 0, v___x_4667_);
    lean_ctor_set(v___x_4668_, 1, v___x_4667_);
    return v___x_4668_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    v___x_4669_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__1);
    v___x_4670_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4670_, 0, v___x_4669_);
    lean_ctor_set(v___x_4670_, 1, v___x_4669_);
    lean_ctor_set(v___x_4670_, 2, v___x_4669_);
    lean_ctor_set(v___x_4670_, 3, v___x_4669_);
    lean_ctor_set(v___x_4670_, 4, v___x_4669_);
    lean_ctor_set(v___x_4670_, 5, v___x_4669_);
    return v___x_4670_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(
    mut v_x_4671_: *mut LeanObject,
    mut v_isExporting_4672_: u8,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4680_: u8 = 0;
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4692_: u8 = 0;
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4705_: u8 = 0;
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4714_: u8 = 0;
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut v_unused_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4727_: u8 = 0;
    let mut v_a_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v_unused_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_unused_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4743_: u8 = 0;
    let mut v_unused_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4678_ = lean_st_ref_get(v___y_4676_);
                v_env_4679_ = lean_ctor_get(v___x_4678_, 0);
                lean_inc_ref(v_env_4679_);
                lean_dec(v___x_4678_);
                v_isExporting_4680_ = lean_ctor_get_uint8(
                    v_env_4679_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_4679_);
                v___x_4681_ = lean_st_ref_take(v___y_4676_);
                v_env_4682_ = lean_ctor_get(v___x_4681_, 0);
                v_nextMacroScope_4683_ = lean_ctor_get(v___x_4681_, 1);
                v_ngen_4684_ = lean_ctor_get(v___x_4681_, 2);
                v_auxDeclNGen_4685_ = lean_ctor_get(v___x_4681_, 3);
                v_traceState_4686_ = lean_ctor_get(v___x_4681_, 4);
                v_messages_4687_ = lean_ctor_get(v___x_4681_, 6);
                v_infoState_4688_ = lean_ctor_get(v___x_4681_, 7);
                v_snapshotTasks_4689_ = lean_ctor_get(v___x_4681_, 8);
                v_isSharedCheck_4743_ = (!lean_is_exclusive(v___x_4681_)) as u8;
                if v_isSharedCheck_4743_ == 0 {
                    v_unused_4744_ = lean_ctor_get(v___x_4681_, 5);
                    lean_dec(v_unused_4744_);
                    v___x_4691_ = v___x_4681_;
                    v_isShared_4692_ = v_isSharedCheck_4743_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4689_);
                    lean_inc(v_infoState_4688_);
                    lean_inc(v_messages_4687_);
                    lean_inc(v_traceState_4686_);
                    lean_inc(v_auxDeclNGen_4685_);
                    lean_inc(v_ngen_4684_);
                    lean_inc(v_nextMacroScope_4683_);
                    lean_inc(v_env_4682_);
                    lean_dec(v___x_4681_);
                    v___x_4691_ = lean_box(0);
                    v_isShared_4692_ = v_isSharedCheck_4743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4693_ = l_Lean_Environment_setExporting(v_env_4682_, v_isExporting_4672_);
                v___x_4694_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__2);
                if v_isShared_4692_ == 0 {
                    lean_ctor_set(v___x_4691_, 5, v___x_4694_);
                    lean_ctor_set(v___x_4691_, 0, v___x_4693_);
                    v___x_4696_ = v___x_4691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4693_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_nextMacroScope_4683_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 2, v_ngen_4684_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 3, v_auxDeclNGen_4685_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 4, v_traceState_4686_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 5, v___x_4694_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 6, v_messages_4687_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 7, v_infoState_4688_);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 8, v_snapshotTasks_4689_);
                    v___x_4696_ = v_reuseFailAlloc_4742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4697_ = lean_st_ref_set(v___y_4676_, v___x_4696_);
                v___x_4698_ = lean_st_ref_take(v___y_4674_);
                v_mctx_4699_ = lean_ctor_get(v___x_4698_, 0);
                v_zetaDeltaFVarIds_4700_ = lean_ctor_get(v___x_4698_, 2);
                v_postponed_4701_ = lean_ctor_get(v___x_4698_, 3);
                v_diag_4702_ = lean_ctor_get(v___x_4698_, 4);
                v_isSharedCheck_4740_ = (!lean_is_exclusive(v___x_4698_)) as u8;
                if v_isSharedCheck_4740_ == 0 {
                    v_unused_4741_ = lean_ctor_get(v___x_4698_, 1);
                    lean_dec(v_unused_4741_);
                    v___x_4704_ = v___x_4698_;
                    v_isShared_4705_ = v_isSharedCheck_4740_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_4702_);
                    lean_inc(v_postponed_4701_);
                    lean_inc(v_zetaDeltaFVarIds_4700_);
                    lean_inc(v_mctx_4699_);
                    lean_dec(v___x_4698_);
                    v___x_4704_ = lean_box(0);
                    v_isShared_4705_ = v_isSharedCheck_4740_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4706_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___closed__3);
                if v_isShared_4705_ == 0 {
                    lean_ctor_set(v___x_4704_, 1, v___x_4706_);
                    v___x_4708_ = v___x_4704_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_mctx_4699_);
                    lean_ctor_set(v_reuseFailAlloc_4739_, 1, v___x_4706_);
                    lean_ctor_set(v_reuseFailAlloc_4739_, 2, v_zetaDeltaFVarIds_4700_);
                    lean_ctor_set(v_reuseFailAlloc_4739_, 3, v_postponed_4701_);
                    lean_ctor_set(v_reuseFailAlloc_4739_, 4, v_diag_4702_);
                    v___x_4708_ = v_reuseFailAlloc_4739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4709_ = lean_st_ref_set(v___y_4674_, v___x_4708_);
                lean_inc(v___y_4676_);
                lean_inc_ref(v___y_4675_);
                lean_inc(v___y_4674_);
                lean_inc_ref(v___y_4673_);
                v_r_4710_ = lean_apply_5(
                    v_x_4671_,
                    v___y_4673_,
                    v___y_4674_,
                    v___y_4675_,
                    v___y_4676_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_4710_) == 0 {
                    v_a_4711_ = lean_ctor_get(v_r_4710_, 0);
                    v_isSharedCheck_4727_ = (!lean_is_exclusive(v_r_4710_)) as u8;
                    if v_isSharedCheck_4727_ == 0 {
                        v___x_4713_ = v_r_4710_;
                        v_isShared_4714_ = v_isSharedCheck_4727_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4711_);
                        lean_dec(v_r_4710_);
                        v___x_4713_ = lean_box(0);
                        v_isShared_4714_ = v_isSharedCheck_4727_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_4728_ = lean_ctor_get(v_r_4710_, 0);
                    lean_inc(v_a_4728_);
                    lean_dec_ref_known(v_r_4710_, 1);
                    v___x_4729_ = lean_box(0);
                    v___x_4730_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_4676_, v_isExporting_4680_, v___x_4694_, v___y_4674_, v___x_4706_, v___x_4729_);
                    v_isSharedCheck_4737_ = (!lean_is_exclusive(v___x_4730_)) as u8;
                    if v_isSharedCheck_4737_ == 0 {
                        v_unused_4738_ = lean_ctor_get(v___x_4730_, 0);
                        lean_dec(v_unused_4738_);
                        v___x_4732_ = v___x_4730_;
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_4730_);
                        v___x_4732_ = lean_box(0);
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_4711_);
                if v_isShared_4714_ == 0 {
                    lean_ctor_set_tag(v___x_4713_, 1);
                    v___x_4716_ = v___x_4713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4711_);
                    v___x_4716_ = v_reuseFailAlloc_4726_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4717_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_4676_, v_isExporting_4680_, v___x_4694_, v___y_4674_, v___x_4706_, v___x_4716_);
                lean_dec_ref(v___x_4716_);
                v_isSharedCheck_4724_ = (!lean_is_exclusive(v___x_4717_)) as u8;
                if v_isSharedCheck_4724_ == 0 {
                    v_unused_4725_ = lean_ctor_get(v___x_4717_, 0);
                    lean_dec(v_unused_4725_);
                    v___x_4719_ = v___x_4717_;
                    v_isShared_4720_ = v_isSharedCheck_4724_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___x_4717_);
                    v___x_4719_ = lean_box(0);
                    v_isShared_4720_ = v_isSharedCheck_4724_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4720_ == 0 {
                    lean_ctor_set(v___x_4719_, 0, v_a_4711_);
                    v___x_4722_ = v___x_4719_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4711_);
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
                    lean_ctor_set_tag(v___x_4732_, 1);
                    lean_ctor_set(v___x_4732_, 0, v_a_4728_);
                    v___x_4735_ = v___x_4732_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4728_);
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
    mut v_x_4745_: *mut LeanObject,
    mut v_isExporting_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4752_: u8 = 0;
    let mut v_res_4753_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4752_ = (lean_unbox(v_isExporting_4746_) as u8);
    v_res_4753_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(v_x_4745_, v_isExporting_boxed_4752_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
    lean_dec(v___y_4750_);
    lean_dec_ref(v___y_4749_);
    lean_dec(v___y_4748_);
    lean_dec_ref(v___y_4747_);
    return v_res_4753_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg(
    mut v_x_4754_: *mut LeanObject,
    mut v_when_4755_: u8,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_4755_ == 0 {
        let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_4759_);
        lean_inc_ref(v___y_4758_);
        lean_inc(v___y_4757_);
        lean_inc_ref(v___y_4756_);
        v___x_4761_ = lean_apply_5(
            v_x_4754_,
            v___y_4756_,
            v___y_4757_,
            v___y_4758_,
            v___y_4759_,
            lean_box(0),
        );
        return v___x_4761_;
    } else {
        let mut v___x_4762_: u8 = 0;
        let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
        v___x_4762_ = 0;
        v___x_4763_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(v_x_4754_, v___x_4762_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
        return v___x_4763_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg___boxed(
    mut v_x_4764_: *mut LeanObject,
    mut v_when_4765_: *mut LeanObject,
    mut v___y_4766_: *mut LeanObject,
    mut v___y_4767_: *mut LeanObject,
    mut v___y_4768_: *mut LeanObject,
    mut v___y_4769_: *mut LeanObject,
    mut v___y_4770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_4771_: u8 = 0;
    let mut v_res_4772_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_4771_ = (lean_unbox(v_when_4765_) as u8);
    v_res_4772_ = l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1___redArg(
        v_x_4764_,
        v_when_boxed_4771_,
        v___y_4766_,
        v___y_4767_,
        v___y_4768_,
        v___y_4769_,
    );
    lean_dec(v___y_4769_);
    lean_dec_ref(v___y_4768_);
    lean_dec(v___y_4767_);
    lean_dec_ref(v___y_4766_);
    return v_res_4772_;
}
pub unsafe fn l_Lean_Meta_reportDiag(
    mut v_a_4773_: *mut LeanObject,
    mut v_a_4774_: *mut LeanObject,
    mut v_a_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: u8 = 0;
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4792_: u8 = 0;
    let mut v_a_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4778_ = l_Lean_isDiagnosticsEnabled___redArg(v_a_4775_);
                if lean_obj_tag(v___x_4778_) == 0 {
                    v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
                    v_isSharedCheck_4792_ = (!lean_is_exclusive(v___x_4778_)) as u8;
                    if v_isSharedCheck_4792_ == 0 {
                        v___x_4781_ = v___x_4778_;
                        v_isShared_4782_ = v_isSharedCheck_4792_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4779_);
                        lean_dec(v___x_4778_);
                        v___x_4781_ = lean_box(0);
                        v_isShared_4782_ = v_isSharedCheck_4792_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4793_ = lean_ctor_get(v___x_4778_, 0);
                    v_isSharedCheck_4800_ = (!lean_is_exclusive(v___x_4778_)) as u8;
                    if v_isSharedCheck_4800_ == 0 {
                        v___x_4795_ = v___x_4778_;
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4793_);
                        lean_dec(v___x_4778_);
                        v___x_4795_ = lean_box(0);
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4783_ = (lean_unbox(v_a_4779_) as u8);
                if v___x_4783_ == 0 {
                    lean_dec(v_a_4779_);
                    v___x_4784_ = lean_box(0);
                    if v_isShared_4782_ == 0 {
                        lean_ctor_set(v___x_4781_, 0, v___x_4784_);
                        v___x_4786_ = v___x_4781_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
                        v___x_4786_ = v_reuseFailAlloc_4787_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4781_);
                    lean_inc_n(v_a_4779_, 2);
                    v___f_4788_ = lean_alloc_closure(
                        l_Lean_Meta_reportDiag___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_4788_, 0, v_a_4779_);
                    v___f_4789_ = lean_alloc_closure(
                        l_Lean_Meta_reportDiag___lam__1___boxed as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    lean_closure_set(v___f_4789_, 0, v_a_4779_);
                    lean_closure_set(v___f_4789_, 1, v___f_4788_);
                    v___x_4790_ = (lean_unbox(v_a_4779_) as u8);
                    lean_dec(v_a_4779_);
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
                    v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
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
    mut v_a_4801_: *mut LeanObject,
    mut v_a_4802_: *mut LeanObject,
    mut v_a_4803_: *mut LeanObject,
    mut v_a_4804_: *mut LeanObject,
    mut v_a_4805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4806_: *mut LeanObject = core::ptr::null_mut();
    v_res_4806_ = l_Lean_Meta_reportDiag(v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
    lean_dec(v_a_4804_);
    lean_dec_ref(v_a_4803_);
    lean_dec(v_a_4802_);
    lean_dec_ref(v_a_4801_);
    return v_res_4806_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2(
    mut v_00_u03b1_4807_: *mut LeanObject,
    mut v_x_4808_: *mut LeanObject,
    mut v_isExporting_4809_: u8,
    mut v___y_4810_: *mut LeanObject,
    mut v___y_4811_: *mut LeanObject,
    mut v___y_4812_: *mut LeanObject,
    mut v___y_4813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    v___x_4815_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___redArg(v_x_4808_, v_isExporting_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
    return v___x_4815_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2___boxed(
    mut v_00_u03b1_4816_: *mut LeanObject,
    mut v_x_4817_: *mut LeanObject,
    mut v_isExporting_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
    mut v___y_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4824_: u8 = 0;
    let mut v_res_4825_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4824_ = (lean_unbox(v_isExporting_4818_) as u8);
    v_res_4825_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1_spec__2(v_00_u03b1_4816_, v_x_4817_, v_isExporting_boxed_4824_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
    lean_dec(v___y_4822_);
    lean_dec_ref(v___y_4821_);
    lean_dec(v___y_4820_);
    lean_dec_ref(v___y_4819_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1(
    mut v_00_u03b1_4826_: *mut LeanObject,
    mut v_x_4827_: *mut LeanObject,
    mut v_when_4828_: u8,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
    mut v___y_4831_: *mut LeanObject,
    mut v___y_4832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4835_: *mut LeanObject,
    mut v_x_4836_: *mut LeanObject,
    mut v_when_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
    mut v___y_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_4843_: u8 = 0;
    let mut v_res_4844_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_4843_ = (lean_unbox(v_when_4837_) as u8);
    v_res_4844_ = l_Lean_withoutExporting___at___00Lean_Meta_reportDiag_spec__1(
        v_00_u03b1_4835_,
        v_x_4836_,
        v_when_boxed_4843_,
        v___y_4838_,
        v___y_4839_,
        v___y_4840_,
        v___y_4841_,
    );
    lean_dec(v___y_4841_);
    lean_dec_ref(v___y_4840_);
    lean_dec(v___y_4839_);
    lean_dec_ref(v___y_4838_);
    return v_res_4844_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Diagnostics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Diagnostics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Diagnostics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Diagnostics(builtin);
}
