// Lean compiler output
// Module: Lean.Meta.LevelDefEq
// Imports: Lean.Util.CollectMVars Lean.Meta.DecLevel Lean.Meta.HasAssignableMVar
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_diagnostics;
use crate::r#gen::Lean::Data::LBool::{l_Bool_toLBool, l_Lean_instBEqLBool_beq};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_getLevelOffset, l_Lean_Level_getOffset, l_Lean_Level_isMVar, l_Lean_Level_isMax,
    l_Lean_Level_isParam, l_Lean_Level_mvarId_x21, l_Lean_Level_normalize, l_Lean_Level_occurs,
    l_Lean_instBEqLevelMVarId_beq, l_Lean_instHashableLevelMVarId_hash, l_Lean_mkLevelMVar,
    l_Lean_mkLevelMax_x27,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofLevel, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_LMVarId_getLevel, l_Lean_LMVarId_isReadOnly, l_Lean_Meta_Context_config,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_mkFreshLevelMVar,
    l_Lean_Meta_throwIsDefEqStuck___redArg,
};
use crate::r#gen::Lean::Meta::DecLevel::{
    initialize_Lean_Meta_DecLevel, l_Lean_Meta_decLevel_x3f, runtime_initialize_Lean_Meta_DecLevel,
};
use crate::r#gen::Lean::Meta::HasAssignableMVar::{
    initialize_Lean_Meta_HasAssignableMVar, l_Lean_Meta_hasAssignableLevelMVar,
    runtime_initialize_Lean_Meta_HasAssignableMVar,
};
use crate::r#gen::Lean::Util::CollectMVars::{
    initialize_Lean_Util_CollectMVars, runtime_initialize_Lean_Util_CollectMVars,
};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_is_level_def_eq;
use crate::lean_imports_rs::Lean::MetavarContext::lean_instantiate_level_mvars;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5, lean_box,
    lean_box_float, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64,
    lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_float, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0_value:
    LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 76, 101, 118, 101, 108, 68, 101, 102, 69, 113,
        0,
    ],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1_value:
    LeanStringObject<55> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 76,
        101, 118, 101, 108, 68, 101, 102, 69, 113, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116,
        97, 46, 115, 111, 108, 118, 101, 83, 101, 108, 102, 77, 97, 120, 0,
    ],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2_value:
    LeanStringObject<32> = LeanStringObject {
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
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 118, 46, 105, 115, 77, 97, 120, 10, 32, 32, 0,
    ],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2_value
)
    as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [77, 101, 116, 97, 0],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [105, 115, 76, 101, 118, 101, 108, 68, 101, 102, 69, 113, 0],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 116, 101, 112, 0],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6_value
)
    as *mut LeanObject;
static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value
        ) as *mut LeanObject,
        142734480563613395 as *mut LeanObject,
    ],
};
static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value
        ) as *mut LeanObject,
        7797271807932843206 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6_value
        ) as *mut LeanObject,
        14740709623910891990 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8_value
        ) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9_value
)
    as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11_value:
    LeanStringObject<15> = LeanStringObject {
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
        115, 111, 108, 118, 101, 83, 101, 108, 102, 77, 97, 120, 58, 32, 0,
    ],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 114, 121, 65, 112, 112, 114, 111, 120, 83, 101, 108, 102, 77, 97, 120, 32, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        116, 114, 121, 65, 112, 112, 114, 111, 120, 77, 97, 120, 77, 97, 120, 32, 0,
    ],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 116, 117, 99, 107, 0],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value
) as *mut LeanObject;
static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value) as *mut LeanObject,7797271807932843206 as *mut LeanObject] };
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value) as *mut LeanObject,1506452367705604955 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 61, 63, 61, 32, 0],
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2: f64 = 0.0;
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__0: f64 = 0.0;
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_isLevelDefEqAuxImpl___closed__4_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [112, 112, 0],
    };
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_isLevelDefEqAuxImpl___closed__5_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 77, 86, 97, 114, 115, 0,
        ],
    };
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__5_value) as *mut LeanObject;
static l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__4_value)
                as *mut LeanObject,
            6746591144584426489 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__5_value) as *mut LeanObject,
        16880101017905244153 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value
            ) as *mut LeanObject,
            142734480563613395 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value
        ) as *mut LeanObject,
        7797271807932843206 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_isLevelDefEqAuxImpl___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [76, 101, 118, 101, 108, 68, 101, 102, 69, 113, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,7969351275899893939 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,10131230049052971294 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,3654788987089858151 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value) as *mut LeanObject,11675043827766884023 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,1719350233513364614 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,7764938331225331255 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,1441607605270172618 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value) as *mut LeanObject,12329077366810606830 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,3434341405050357539 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,((( 1935786688 as usize) << 1) | 1) as *mut LeanObject,1289442465053804558 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,14432860239818490969 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,8013777916234352017 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,10035472403340776044 as *mut LeanObject] };
static mut l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(
    mut v_lvl_2073_: *mut LeanObject,
    mut v_a_2074_: *mut LeanObject,
) -> u8 {
    let mut v_a_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: u8 = 0;
    let mut v___x_2081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2074_) == 2 {
                    v_a_2075_ = lean_ctor_get(v_a_2074_, 0);
                    v_a_2076_ = lean_ctor_get(v_a_2074_, 1);
                    v___x_2077_ =
                        l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(
                            v_lvl_2073_,
                            v_a_2075_,
                        );
                    if v___x_2077_ == 0 {
                        v_a_2074_ = v_a_2076_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2077_;
                    }
                } else {
                    v___x_2079_ = lean_level_eq(v_a_2074_, v_lvl_2073_);
                    if v___x_2079_ == 0 {
                        v___x_2080_ = l_Lean_Level_occurs(v_lvl_2073_, v_a_2074_);
                        return v___x_2080_;
                    } else {
                        v___x_2081_ = 0;
                        return v___x_2081_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(
    mut v_lvl_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2084_: u8 = 0;
    let mut v_r_2085_: *mut LeanObject = core::ptr::null_mut();
    v_res_2084_ =
        l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_2082_, v_a_2083_);
    lean_dec(v_a_2083_);
    lean_dec(v_lvl_2082_);
    v_r_2085_ = lean_box((v_res_2084_) as usize);
    return v_r_2085_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(
    mut v_lvl_2086_: *mut LeanObject,
    mut v_x_2087_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2087_) == 2 {
        let mut v_a_2088_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: u8 = 0;
        v_a_2088_ = lean_ctor_get(v_x_2087_, 0);
        v_a_2089_ = lean_ctor_get(v_x_2087_, 1);
        v___x_2090_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(
            v_lvl_2086_,
            v_a_2088_,
        );
        if v___x_2090_ == 0 {
            let mut v___x_2091_: u8 = 0;
            v___x_2091_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(
                v_lvl_2086_,
                v_a_2089_,
            );
            return v___x_2091_;
        } else {
            return v___x_2090_;
        }
    } else {
        let mut v___x_2092_: u8 = 0;
        v___x_2092_ = 0;
        return v___x_2092_;
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(
    mut v_lvl_2093_: *mut LeanObject,
    mut v_x_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2095_: u8 = 0;
    let mut v_r_2096_: *mut LeanObject = core::ptr::null_mut();
    v_res_2095_ =
        l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_lvl_2093_, v_x_2094_);
    lean_dec(v_x_2094_);
    lean_dec(v_lvl_2093_);
    v_r_2096_ = lean_box((v_res_2095_) as usize);
    return v_r_2096_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(
    mut v_mvarId_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
    mut v_x_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: u8 = 0;
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2098_) {
                2 => {
                    v_a_2100_ = lean_ctor_get(v_x_2098_, 0);
                    lean_inc(v_a_2100_);
                    v_a_2101_ = lean_ctor_get(v_x_2098_, 1);
                    lean_inc(v_a_2101_);
                    lean_dec_ref_known(v_x_2098_, 2);
                    v___x_2102_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(
                        v_mvarId_2097_,
                        v_a_2100_,
                        v_x_2099_,
                    );
                    v_x_2098_ = v_a_2101_;
                    v_x_2099_ = v___x_2102_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_a_2104_ = lean_ctor_get(v_x_2098_, 0);
                    v___x_2105_ = l_Lean_instBEqLevelMVarId_beq(v_a_2104_, v_mvarId_2097_);
                    if v___x_2105_ == 0 {
                        v___x_2106_ = l_Lean_mkLevelMax_x27(v_x_2099_, v_x_2098_);
                        return v___x_2106_;
                    } else {
                        lean_dec_ref_known(v_x_2098_, 1);
                        return v_x_2099_;
                    }
                }
                _ => {
                    v___x_2107_ = l_Lean_mkLevelMax_x27(v_x_2099_, v_x_2098_);
                    return v___x_2107_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(
    mut v_mvarId_2108_: *mut LeanObject,
    mut v_x_2109_: *mut LeanObject,
    mut v_x_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2111_: *mut LeanObject = core::ptr::null_mut();
    v_res_2111_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(
        v_mvarId_2108_,
        v_x_2109_,
        v_x_2110_,
    );
    lean_dec(v_mvarId_2108_);
    return v_res_2111_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(
    mut v_msg_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320__overap_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    v___f_2119_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0;
    v___x_1320__overap_2120_ = lean_panic_fn_borrowed(v___f_2119_, v_msg_2113_);
    lean_inc(v___y_2117_);
    lean_inc_ref(v___y_2116_);
    lean_inc(v___y_2115_);
    lean_inc_ref(v___y_2114_);
    v___x_2121_ = lean_apply_5(
        v___x_1320__overap_2120_,
        v___y_2114_,
        v___y_2115_,
        v___y_2116_,
        v___y_2117_,
        lean_box(0),
    );
    return v___x_2121_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___boxed(
    mut v_msg_2122_: *mut LeanObject,
    mut v___y_2123_: *mut LeanObject,
    mut v___y_2124_: *mut LeanObject,
    mut v___y_2125_: *mut LeanObject,
    mut v___y_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2128_: *mut LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(
        v_msg_2122_,
        v___y_2123_,
        v___y_2124_,
        v___y_2125_,
        v___y_2126_,
    );
    lean_dec(v___y_2126_);
    lean_dec_ref(v___y_2125_);
    lean_dec(v___y_2124_);
    lean_dec_ref(v___y_2123_);
    return v_res_2128_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(
    mut v_x_2129_: *mut LeanObject,
    mut v_x_2130_: *mut LeanObject,
    mut v_x_2131_: *mut LeanObject,
    mut v_x_2132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2137_: u8 = 0;
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2133_ = lean_ctor_get(v_x_2129_, 0);
                v_vs_2134_ = lean_ctor_get(v_x_2129_, 1);
                v_isSharedCheck_2158_ = (!lean_is_exclusive(v_x_2129_)) as u8;
                if v_isSharedCheck_2158_ == 0 {
                    v___x_2136_ = v_x_2129_;
                    v_isShared_2137_ = v_isSharedCheck_2158_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2134_);
                    lean_inc(v_ks_2133_);
                    lean_dec(v_x_2129_);
                    v___x_2136_ = lean_box(0);
                    v_isShared_2137_ = v_isSharedCheck_2158_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2138_ = lean_array_get_size(v_ks_2133_);
                v___x_2139_ = lean_nat_dec_lt(v_x_2130_, v___x_2138_);
                if v___x_2139_ == 0 {
                    lean_dec(v_x_2130_);
                    v___x_2140_ = lean_array_push(v_ks_2133_, v_x_2131_);
                    v___x_2141_ = lean_array_push(v_vs_2134_, v_x_2132_);
                    if v_isShared_2137_ == 0 {
                        lean_ctor_set(v___x_2136_, 1, v___x_2141_);
                        lean_ctor_set(v___x_2136_, 0, v___x_2140_);
                        v___x_2143_ = v___x_2136_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2140_);
                        lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2141_);
                        v___x_2143_ = v_reuseFailAlloc_2144_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2145_ = lean_array_fget_borrowed(v_ks_2133_, v_x_2130_);
                    v___x_2146_ = l_Lean_instBEqLevelMVarId_beq(v_x_2131_, v_k_x27_2145_);
                    if v___x_2146_ == 0 {
                        if v_isShared_2137_ == 0 {
                            v___x_2148_ = v___x_2136_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_ks_2133_);
                            lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_vs_2134_);
                            v___x_2148_ = v_reuseFailAlloc_2152_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2153_ = lean_array_fset(v_ks_2133_, v_x_2130_, v_x_2131_);
                        v___x_2154_ = lean_array_fset(v_vs_2134_, v_x_2130_, v_x_2132_);
                        lean_dec(v_x_2130_);
                        if v_isShared_2137_ == 0 {
                            lean_ctor_set(v___x_2136_, 1, v___x_2154_);
                            lean_ctor_set(v___x_2136_, 0, v___x_2153_);
                            v___x_2156_ = v___x_2136_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2153_);
                            lean_ctor_set(v_reuseFailAlloc_2157_, 1, v___x_2154_);
                            v___x_2156_ = v_reuseFailAlloc_2157_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2143_;
            }
            3 => {
                v___x_2149_ = lean_unsigned_to_nat(1);
                v___x_2150_ = lean_nat_add(v_x_2130_, v___x_2149_);
                lean_dec(v_x_2130_);
                v_x_2129_ = v___x_2148_;
                v_x_2130_ = v___x_2150_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(
    mut v_n_2159_: *mut LeanObject,
    mut v_k_2160_: *mut LeanObject,
    mut v_v_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    v___x_2162_ = lean_unsigned_to_nat(0);
    v___x_2163_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_n_2159_, v___x_2162_, v_k_2160_, v_v_2161_);
    return v___x_2163_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2164_: usize = 0;
    let mut v___x_2165_: usize = 0;
    let mut v___x_2166_: usize = 0;
    v___x_2164_ = 5usize;
    v___x_2165_ = 1usize;
    v___x_2166_ = lean_usize_shift_left(v___x_2165_, v___x_2164_);
    return v___x_2166_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2167_: usize = 0;
    let mut v___x_2168_: usize = 0;
    let mut v___x_2169_: usize = 0;
    v___x_2167_ = 1usize;
    v___x_2168_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0);
    v___x_2169_ = lean_usize_sub(v___x_2168_, v___x_2167_);
    return v___x_2169_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    v___x_2170_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2170_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(
    mut v_x_2171_: *mut LeanObject,
    mut v_x_2172_: usize,
    mut v_x_2173_: usize,
    mut v_x_2174_: *mut LeanObject,
    mut v_x_2175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: usize = 0;
    let mut v___x_2178_: usize = 0;
    let mut v___x_2179_: usize = 0;
    let mut v___x_2180_: usize = 0;
    let mut v_j_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v_v_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: u8 = 0;
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_node_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2211_: u8 = 0;
    let mut v___x_2212_: usize = 0;
    let mut v___x_2213_: usize = 0;
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2220_: u8 = 0;
    let mut v_unused_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: u8 = 0;
    let mut v_ks_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v_reuseFailAlloc_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2171_) == 0 {
                    v_es_2176_ = lean_ctor_get(v_x_2171_, 0);
                    v___x_2177_ = 5usize;
                    v___x_2178_ = 1usize;
                    v___x_2179_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1);
                    v___x_2180_ = lean_usize_land(v_x_2172_, v___x_2179_);
                    v_j_2181_ = lean_usize_to_nat(v___x_2180_);
                    v___x_2182_ = lean_array_get_size(v_es_2176_);
                    v___x_2183_ = lean_nat_dec_lt(v_j_2181_, v___x_2182_);
                    if v___x_2183_ == 0 {
                        lean_dec(v_j_2181_);
                        lean_dec(v_x_2175_);
                        lean_dec(v_x_2174_);
                        return v_x_2171_;
                    } else {
                        lean_inc_ref(v_es_2176_);
                        v_isSharedCheck_2220_ = (!lean_is_exclusive(v_x_2171_)) as u8;
                        if v_isSharedCheck_2220_ == 0 {
                            v_unused_2221_ = lean_ctor_get(v_x_2171_, 0);
                            lean_dec(v_unused_2221_);
                            v___x_2185_ = v_x_2171_;
                            v_isShared_2186_ = v_isSharedCheck_2220_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2171_);
                            v___x_2185_ = lean_box(0);
                            v_isShared_2186_ = v_isSharedCheck_2220_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2222_ = lean_ctor_get(v_x_2171_, 0);
                    v_vs_2223_ = lean_ctor_get(v_x_2171_, 1);
                    v_isSharedCheck_2243_ = (!lean_is_exclusive(v_x_2171_)) as u8;
                    if v_isSharedCheck_2243_ == 0 {
                        v___x_2225_ = v_x_2171_;
                        v_isShared_2226_ = v_isSharedCheck_2243_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2223_);
                        lean_inc(v_ks_2222_);
                        lean_dec(v_x_2171_);
                        v___x_2225_ = lean_box(0);
                        v_isShared_2226_ = v_isSharedCheck_2243_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2187_ = lean_array_fget(v_es_2176_, v_j_2181_);
                v___x_2188_ = lean_box(0);
                v_xs_x27_2189_ = lean_array_fset(v_es_2176_, v_j_2181_, v___x_2188_);
                match lean_obj_tag(v_v_2187_) {
                    0 => {
                        v_key_2196_ = lean_ctor_get(v_v_2187_, 0);
                        v_val_2197_ = lean_ctor_get(v_v_2187_, 1);
                        v_isSharedCheck_2207_ = (!lean_is_exclusive(v_v_2187_)) as u8;
                        if v_isSharedCheck_2207_ == 0 {
                            v___x_2199_ = v_v_2187_;
                            v_isShared_2200_ = v_isSharedCheck_2207_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2197_);
                            lean_inc(v_key_2196_);
                            lean_dec(v_v_2187_);
                            v___x_2199_ = lean_box(0);
                            v_isShared_2200_ = v_isSharedCheck_2207_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2208_ = lean_ctor_get(v_v_2187_, 0);
                        v_isSharedCheck_2218_ = (!lean_is_exclusive(v_v_2187_)) as u8;
                        if v_isSharedCheck_2218_ == 0 {
                            v___x_2210_ = v_v_2187_;
                            v_isShared_2211_ = v_isSharedCheck_2218_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2208_);
                            lean_dec(v_v_2187_);
                            v___x_2210_ = lean_box(0);
                            v_isShared_2211_ = v_isSharedCheck_2218_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2219_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2219_, 0, v_x_2174_);
                        lean_ctor_set(v___x_2219_, 1, v_x_2175_);
                        v___y_2191_ = v___x_2219_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2192_ = lean_array_fset(v_xs_x27_2189_, v_j_2181_, v___y_2191_);
                lean_dec(v_j_2181_);
                if v_isShared_2186_ == 0 {
                    lean_ctor_set(v___x_2185_, 0, v___x_2192_);
                    v___x_2194_ = v___x_2185_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
                    v___x_2194_ = v_reuseFailAlloc_2195_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2194_;
            }
            4 => {
                v___x_2201_ = l_Lean_instBEqLevelMVarId_beq(v_x_2174_, v_key_2196_);
                if v___x_2201_ == 0 {
                    lean_del_object(v___x_2199_);
                    v___x_2202_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2196_,
                        v_val_2197_,
                        v_x_2174_,
                        v_x_2175_,
                    );
                    v___x_2203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2203_, 0, v___x_2202_);
                    v___y_2191_ = v___x_2203_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2197_);
                    lean_dec(v_key_2196_);
                    if v_isShared_2200_ == 0 {
                        lean_ctor_set(v___x_2199_, 1, v_x_2175_);
                        lean_ctor_set(v___x_2199_, 0, v_x_2174_);
                        v___x_2205_ = v___x_2199_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_x_2174_);
                        lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_x_2175_);
                        v___x_2205_ = v_reuseFailAlloc_2206_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2191_ = v___x_2205_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2212_ = lean_usize_shift_right(v_x_2172_, v___x_2177_);
                v___x_2213_ = lean_usize_add(v_x_2173_, v___x_2178_);
                v___x_2214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_node_2208_, v___x_2212_, v___x_2213_, v_x_2174_, v_x_2175_);
                if v_isShared_2211_ == 0 {
                    lean_ctor_set(v___x_2210_, 0, v___x_2214_);
                    v___x_2216_ = v___x_2210_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
                    v___x_2216_ = v_reuseFailAlloc_2217_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2191_ = v___x_2216_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2226_ == 0 {
                    v___x_2228_ = v___x_2225_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_ks_2222_);
                    lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_vs_2223_);
                    v___x_2228_ = v_reuseFailAlloc_2242_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2229_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v___x_2228_, v_x_2174_, v_x_2175_);
                v___x_2237_ = 7usize;
                v___x_2238_ = lean_usize_dec_le(v___x_2237_, v_x_2173_);
                if v___x_2238_ == 0 {
                    v___x_2239_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2229_);
                    v___x_2240_ = lean_unsigned_to_nat(4);
                    v___x_2241_ = lean_nat_dec_lt(v___x_2239_, v___x_2240_);
                    lean_dec(v___x_2239_);
                    v___y_2231_ = v___x_2241_;
                    state = 10;
                    continue;
                } else {
                    v___y_2231_ = v___x_2238_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2231_ == 0 {
                    v_ks_2232_ = lean_ctor_get(v_newNode_2229_, 0);
                    lean_inc_ref(v_ks_2232_);
                    v_vs_2233_ = lean_ctor_get(v_newNode_2229_, 1);
                    lean_inc_ref(v_vs_2233_);
                    lean_dec_ref(v_newNode_2229_);
                    v___x_2234_ = lean_unsigned_to_nat(0);
                    v___x_2235_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2);
                    v___x_2236_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_x_2173_, v_ks_2232_, v_vs_2233_, v___x_2234_, v___x_2235_);
                    lean_dec_ref(v_vs_2233_);
                    lean_dec_ref(v_ks_2232_);
                    return v___x_2236_;
                } else {
                    return v_newNode_2229_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(
    mut v_depth_2244_: usize,
    mut v_keys_2245_: *mut LeanObject,
    mut v_vals_2246_: *mut LeanObject,
    mut v_i_2247_: *mut LeanObject,
    mut v_entries_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: u8 = 0;
    let mut v_k_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u64 = 0;
    let mut v_h_2254_: usize = 0;
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2259_: usize = 0;
    let mut v_h_2260_: usize = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2249_ = lean_array_get_size(v_keys_2245_);
                v___x_2250_ = lean_nat_dec_lt(v_i_2247_, v___x_2249_);
                if v___x_2250_ == 0 {
                    lean_dec(v_i_2247_);
                    return v_entries_2248_;
                } else {
                    v_k_2251_ = lean_array_fget_borrowed(v_keys_2245_, v_i_2247_);
                    v_v_2252_ = lean_array_fget_borrowed(v_vals_2246_, v_i_2247_);
                    v___x_2253_ = l_Lean_instHashableLevelMVarId_hash(v_k_2251_);
                    v_h_2254_ = lean_uint64_to_usize(v___x_2253_);
                    v___x_2255_ = 5usize;
                    v___x_2256_ = lean_unsigned_to_nat(1);
                    v___x_2257_ = 1usize;
                    v___x_2258_ = lean_usize_sub(v_depth_2244_, v___x_2257_);
                    v___x_2259_ = lean_usize_mul(v___x_2255_, v___x_2258_);
                    v_h_2260_ = lean_usize_shift_right(v_h_2254_, v___x_2259_);
                    v___x_2261_ = lean_nat_add(v_i_2247_, v___x_2256_);
                    lean_dec(v_i_2247_);
                    lean_inc(v_v_2252_);
                    lean_inc(v_k_2251_);
                    v___x_2262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_entries_2248_, v_h_2260_, v_depth_2244_, v_k_2251_, v_v_2252_);
                    v_i_2247_ = v___x_2261_;
                    v_entries_2248_ = v___x_2262_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_depth_2264_: *mut LeanObject,
    mut v_keys_2265_: *mut LeanObject,
    mut v_vals_2266_: *mut LeanObject,
    mut v_i_2267_: *mut LeanObject,
    mut v_entries_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2269_: usize = 0;
    let mut v_res_2270_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2269_ = lean_unbox_usize(v_depth_2264_);
    lean_dec(v_depth_2264_);
    v_res_2270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_boxed_2269_, v_keys_2265_, v_vals_2266_, v_i_2267_, v_entries_2268_);
    lean_dec_ref(v_vals_2266_);
    lean_dec_ref(v_keys_2265_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_2271_: *mut LeanObject,
    mut v_x_2272_: *mut LeanObject,
    mut v_x_2273_: *mut LeanObject,
    mut v_x_2274_: *mut LeanObject,
    mut v_x_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3043__boxed_2276_: usize = 0;
    let mut v_x_3044__boxed_2277_: usize = 0;
    let mut v_res_2278_: *mut LeanObject = core::ptr::null_mut();
    v_x_3043__boxed_2276_ = lean_unbox_usize(v_x_2272_);
    lean_dec(v_x_2272_);
    v_x_3044__boxed_2277_ = lean_unbox_usize(v_x_2273_);
    lean_dec(v_x_2273_);
    v_res_2278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_2271_, v_x_3043__boxed_2276_, v_x_3044__boxed_2277_, v_x_2274_, v_x_2275_);
    return v_res_2278_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(
    mut v_x_2279_: *mut LeanObject,
    mut v_x_2280_: *mut LeanObject,
    mut v_x_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2282_: u64 = 0;
    let mut v___x_2283_: usize = 0;
    let mut v___x_2284_: usize = 0;
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    v___x_2282_ = l_Lean_instHashableLevelMVarId_hash(v_x_2280_);
    v___x_2283_ = lean_uint64_to_usize(v___x_2282_);
    v___x_2284_ = 1usize;
    v___x_2285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_2279_, v___x_2283_, v___x_2284_, v_x_2280_, v_x_2281_);
    return v___x_2285_;
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(
    mut v_mvarId_2286_: *mut LeanObject,
    mut v_val_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v_depth_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2290_ = lean_st_ref_take(v___y_2288_);
                v_mctx_2291_ = lean_ctor_get(v___x_2290_, 0);
                v_cache_2292_ = lean_ctor_get(v___x_2290_, 1);
                v_zetaDeltaFVarIds_2293_ = lean_ctor_get(v___x_2290_, 2);
                v_postponed_2294_ = lean_ctor_get(v___x_2290_, 3);
                v_diag_2295_ = lean_ctor_get(v___x_2290_, 4);
                v_isSharedCheck_2323_ = (!lean_is_exclusive(v___x_2290_)) as u8;
                if v_isSharedCheck_2323_ == 0 {
                    v___x_2297_ = v___x_2290_;
                    v_isShared_2298_ = v_isSharedCheck_2323_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_2295_);
                    lean_inc(v_postponed_2294_);
                    lean_inc(v_zetaDeltaFVarIds_2293_);
                    lean_inc(v_cache_2292_);
                    lean_inc(v_mctx_2291_);
                    lean_dec(v___x_2290_);
                    v___x_2297_ = lean_box(0);
                    v_isShared_2298_ = v_isSharedCheck_2323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2299_ = lean_ctor_get(v_mctx_2291_, 0);
                v_levelAssignDepth_2300_ = lean_ctor_get(v_mctx_2291_, 1);
                v_lmvarCounter_2301_ = lean_ctor_get(v_mctx_2291_, 2);
                v_mvarCounter_2302_ = lean_ctor_get(v_mctx_2291_, 3);
                v_lDecls_2303_ = lean_ctor_get(v_mctx_2291_, 4);
                v_decls_2304_ = lean_ctor_get(v_mctx_2291_, 5);
                v_userNames_2305_ = lean_ctor_get(v_mctx_2291_, 6);
                v_lAssignment_2306_ = lean_ctor_get(v_mctx_2291_, 7);
                v_eAssignment_2307_ = lean_ctor_get(v_mctx_2291_, 8);
                v_dAssignment_2308_ = lean_ctor_get(v_mctx_2291_, 9);
                v_isSharedCheck_2322_ = (!lean_is_exclusive(v_mctx_2291_)) as u8;
                if v_isSharedCheck_2322_ == 0 {
                    v___x_2310_ = v_mctx_2291_;
                    v_isShared_2311_ = v_isSharedCheck_2322_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_2308_);
                    lean_inc(v_eAssignment_2307_);
                    lean_inc(v_lAssignment_2306_);
                    lean_inc(v_userNames_2305_);
                    lean_inc(v_decls_2304_);
                    lean_inc(v_lDecls_2303_);
                    lean_inc(v_mvarCounter_2302_);
                    lean_inc(v_lmvarCounter_2301_);
                    lean_inc(v_levelAssignDepth_2300_);
                    lean_inc(v_depth_2299_);
                    lean_dec(v_mctx_2291_);
                    v___x_2310_ = lean_box(0);
                    v_isShared_2311_ = v_isSharedCheck_2322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2312_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_2306_, v_mvarId_2286_, v_val_2287_);
                if v_isShared_2311_ == 0 {
                    lean_ctor_set(v___x_2310_, 7, v___x_2312_);
                    v___x_2314_ = v___x_2310_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_depth_2299_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_levelAssignDepth_2300_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_lmvarCounter_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_mvarCounter_2302_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_lDecls_2303_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_decls_2304_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 6, v_userNames_2305_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 7, v___x_2312_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 8, v_eAssignment_2307_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 9, v_dAssignment_2308_);
                    v___x_2314_ = v_reuseFailAlloc_2321_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2298_ == 0 {
                    lean_ctor_set(v___x_2297_, 0, v___x_2314_);
                    v___x_2316_ = v___x_2297_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2314_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_cache_2292_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_zetaDeltaFVarIds_2293_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_postponed_2294_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_diag_2295_);
                    v___x_2316_ = v_reuseFailAlloc_2320_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2317_ = lean_st_ref_set(v___y_2288_, v___x_2316_);
                v___x_2318_ = lean_box(0);
                v___x_2319_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2319_, 0, v___x_2318_);
                return v___x_2319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(
    mut v_mvarId_2324_: *mut LeanObject,
    mut v_val_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2324_, v_val_2325_, v___y_2326_);
    lean_dec(v___y_2326_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(
    mut v_msgData_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    v___x_2335_ = lean_st_ref_get(v___y_2333_);
    v_env_2336_ = lean_ctor_get(v___x_2335_, 0);
    lean_inc_ref(v_env_2336_);
    lean_dec(v___x_2335_);
    v___x_2337_ = lean_st_ref_get(v___y_2331_);
    v_mctx_2338_ = lean_ctor_get(v___x_2337_, 0);
    lean_inc_ref(v_mctx_2338_);
    lean_dec(v___x_2337_);
    v_lctx_2339_ = lean_ctor_get(v___y_2330_, 2);
    v_options_2340_ = lean_ctor_get(v___y_2332_, 2);
    lean_inc_ref(v_options_2340_);
    lean_inc_ref(v_lctx_2339_);
    v___x_2341_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2341_, 0, v_env_2336_);
    lean_ctor_set(v___x_2341_, 1, v_mctx_2338_);
    lean_ctor_set(v___x_2341_, 2, v_lctx_2339_);
    lean_ctor_set(v___x_2341_, 3, v_options_2340_);
    v___x_2342_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2342_, 0, v___x_2341_);
    lean_ctor_set(v___x_2342_, 1, v_msgData_2329_);
    v___x_2343_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2343_, 0, v___x_2342_);
    return v___x_2343_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(
    mut v_msgData_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2350_: *mut LeanObject = core::ptr::null_mut();
    v_res_2350_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
    lean_dec(v___y_2348_);
    lean_dec_ref(v___y_2347_);
    lean_dec(v___y_2346_);
    lean_dec_ref(v___y_2345_);
    return v_res_2350_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0()
-> f64 {
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: f64 = 0.0;
    v___x_2351_ = lean_unsigned_to_nat(0);
    v___x_2352_ = lean_float_of_nat(v___x_2351_);
    return v___x_2352_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(
    mut v_cls_2356_: *mut LeanObject,
    mut v_msg_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2368_: u8 = 0;
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2381_: u8 = 0;
    let mut v_tid_2382_: u64 = 0;
    let mut v_traces_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: f64 = 0.0;
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut v_isSharedCheck_2409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2363_ = lean_ctor_get(v___y_2360_, 5);
                v___x_2364_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
                v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
                v_isSharedCheck_2409_ = (!lean_is_exclusive(v___x_2364_)) as u8;
                if v_isSharedCheck_2409_ == 0 {
                    v___x_2367_ = v___x_2364_;
                    v_isShared_2368_ = v_isSharedCheck_2409_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2365_);
                    lean_dec(v___x_2364_);
                    v___x_2367_ = lean_box(0);
                    v_isShared_2368_ = v_isSharedCheck_2409_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2369_ = lean_st_ref_take(v___y_2361_);
                v_traceState_2370_ = lean_ctor_get(v___x_2369_, 4);
                v_env_2371_ = lean_ctor_get(v___x_2369_, 0);
                v_nextMacroScope_2372_ = lean_ctor_get(v___x_2369_, 1);
                v_ngen_2373_ = lean_ctor_get(v___x_2369_, 2);
                v_auxDeclNGen_2374_ = lean_ctor_get(v___x_2369_, 3);
                v_cache_2375_ = lean_ctor_get(v___x_2369_, 5);
                v_messages_2376_ = lean_ctor_get(v___x_2369_, 6);
                v_infoState_2377_ = lean_ctor_get(v___x_2369_, 7);
                v_snapshotTasks_2378_ = lean_ctor_get(v___x_2369_, 8);
                v_isSharedCheck_2408_ = (!lean_is_exclusive(v___x_2369_)) as u8;
                if v_isSharedCheck_2408_ == 0 {
                    v___x_2380_ = v___x_2369_;
                    v_isShared_2381_ = v_isSharedCheck_2408_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2378_);
                    lean_inc(v_infoState_2377_);
                    lean_inc(v_messages_2376_);
                    lean_inc(v_cache_2375_);
                    lean_inc(v_traceState_2370_);
                    lean_inc(v_auxDeclNGen_2374_);
                    lean_inc(v_ngen_2373_);
                    lean_inc(v_nextMacroScope_2372_);
                    lean_inc(v_env_2371_);
                    lean_dec(v___x_2369_);
                    v___x_2380_ = lean_box(0);
                    v_isShared_2381_ = v_isSharedCheck_2408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2382_ = lean_ctor_get_uint64(
                    v_traceState_2370_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2383_ = lean_ctor_get(v_traceState_2370_, 0);
                v_isSharedCheck_2407_ = (!lean_is_exclusive(v_traceState_2370_)) as u8;
                if v_isSharedCheck_2407_ == 0 {
                    v___x_2385_ = v_traceState_2370_;
                    v_isShared_2386_ = v_isSharedCheck_2407_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2383_);
                    lean_dec(v_traceState_2370_);
                    v___x_2385_ = lean_box(0);
                    v_isShared_2386_ = v_isSharedCheck_2407_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2387_ = lean_box(0);
                v___x_2388_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
                v___x_2389_ = 0;
                v___x_2390_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1;
                v___x_2391_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2391_, 0, v_cls_2356_);
                lean_ctor_set(v___x_2391_, 1, v___x_2387_);
                lean_ctor_set(v___x_2391_, 2, v___x_2390_);
                lean_ctor_set_float(
                    v___x_2391_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2388_,
                );
                lean_ctor_set_float(
                    v___x_2391_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2388_,
                );
                lean_ctor_set_uint8(
                    v___x_2391_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2389_,
                );
                v___x_2392_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2;
                v___x_2393_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2393_, 0, v___x_2391_);
                lean_ctor_set(v___x_2393_, 1, v_a_2365_);
                lean_ctor_set(v___x_2393_, 2, v___x_2392_);
                lean_inc(v_ref_2363_);
                v___x_2394_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2394_, 0, v_ref_2363_);
                lean_ctor_set(v___x_2394_, 1, v___x_2393_);
                v___x_2395_ = l_Lean_PersistentArray_push___redArg(v_traces_2383_, v___x_2394_);
                if v_isShared_2386_ == 0 {
                    lean_ctor_set(v___x_2385_, 0, v___x_2395_);
                    v___x_2397_ = v___x_2385_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2395_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2406_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2382_,
                    );
                    v___x_2397_ = v_reuseFailAlloc_2406_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2381_ == 0 {
                    lean_ctor_set(v___x_2380_, 4, v___x_2397_);
                    v___x_2399_ = v___x_2380_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_env_2371_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_nextMacroScope_2372_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_ngen_2373_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_auxDeclNGen_2374_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 4, v___x_2397_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 5, v_cache_2375_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 6, v_messages_2376_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 7, v_infoState_2377_);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 8, v_snapshotTasks_2378_);
                    v___x_2399_ = v_reuseFailAlloc_2405_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2400_ = lean_st_ref_set(v___y_2361_, v___x_2399_);
                v___x_2401_ = lean_box(0);
                if v_isShared_2368_ == 0 {
                    lean_ctor_set(v___x_2367_, 0, v___x_2401_);
                    v___x_2403_ = v___x_2367_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
                    v___x_2403_ = v_reuseFailAlloc_2404_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(
    mut v_cls_2410_: *mut LeanObject,
    mut v_msg_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v_res_2417_ =
        l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(
            v_cls_2410_,
            v_msg_2411_,
            v___y_2412_,
            v___y_2413_,
            v___y_2414_,
            v___y_2415_,
        );
    lean_dec(v___y_2415_);
    lean_dec_ref(v___y_2414_);
    lean_dec(v___y_2413_);
    lean_dec_ref(v___y_2412_);
    return v_res_2417_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3()
-> *mut LeanObject {
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    v___x_2421_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2;
    v___x_2422_ = lean_unsigned_to_nat(2);
    v___x_2423_ = lean_unsigned_to_nat(39);
    v___x_2424_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
    v___x_2425_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0;
    v___x_2426_ = l_mkPanicMessageWithDecl(
        v___x_2425_,
        v___x_2424_,
        v___x_2423_,
        v___x_2422_,
        v___x_2421_,
    );
    return v___x_2426_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10()
-> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
    v___x_2438_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9;
    v___x_2439_ = l_Lean_Name_append(v___x_2438_, v___x_2437_);
    return v___x_2439_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12()
-> *mut LeanObject {
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    v___x_2441_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11;
    v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
    return v___x_2442_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14()
-> *mut LeanObject {
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    v___x_2444_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13;
    v___x_2445_ = l_Lean_stringToMessageData(v___x_2444_);
    return v___x_2445_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(
    mut v_mvarId_2446_: *mut LeanObject,
    mut v_v_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
    mut v_a_2450_: *mut LeanObject,
    mut v_a_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2460_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2453_ = l_Lean_Level_isMax(v_v_2447_);
                if v___x_2453_ == 0 {
                    lean_dec(v_v_2447_);
                    lean_dec(v_mvarId_2446_);
                    v___x_2454_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
                    v___x_2455_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_2454_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
                    return v___x_2455_;
                } else {
                    v___x_2456_ =
                        l_Lean_Meta_mkFreshLevelMVar(v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
                    if lean_obj_tag(v___x_2456_) == 0 {
                        v_options_2457_ = lean_ctor_get(v_a_2450_, 2);
                        v_a_2458_ = lean_ctor_get(v___x_2456_, 0);
                        lean_inc(v_a_2458_);
                        lean_dec_ref_known(v___x_2456_, 1);
                        v_inheritedTraceOptions_2459_ = lean_ctor_get(v_a_2450_, 13);
                        v_hasTrace_2460_ = lean_ctor_get_uint8(
                            v_options_2457_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        v___x_2461_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(
                            v_mvarId_2446_,
                            v_v_2447_,
                            v_a_2458_,
                        );
                        if v_hasTrace_2460_ == 0 {
                            v___x_2462_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2446_, v___x_2461_, v_a_2449_);
                            return v___x_2462_;
                        } else {
                            v___x_2463_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
                            v___x_2464_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
                            v___x_2465_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2459_,
                                v_options_2457_,
                                v___x_2464_,
                            );
                            if v___x_2465_ == 0 {
                                v___x_2466_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2446_, v___x_2461_, v_a_2449_);
                                return v___x_2466_;
                            } else {
                                v___x_2467_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
                                lean_inc(v_mvarId_2446_);
                                v___x_2468_ = l_Lean_mkLevelMVar(v_mvarId_2446_);
                                v___x_2469_ = l_Lean_MessageData_ofLevel(v___x_2468_);
                                v___x_2470_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2470_, 0, v___x_2467_);
                                lean_ctor_set(v___x_2470_, 1, v___x_2469_);
                                v___x_2471_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
                                v___x_2472_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2472_, 0, v___x_2470_);
                                lean_ctor_set(v___x_2472_, 1, v___x_2471_);
                                lean_inc(v___x_2461_);
                                v___x_2473_ = l_Lean_MessageData_ofLevel(v___x_2461_);
                                v___x_2474_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2474_, 0, v___x_2472_);
                                lean_ctor_set(v___x_2474_, 1, v___x_2473_);
                                v___x_2475_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_2463_, v___x_2474_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
                                if lean_obj_tag(v___x_2475_) == 0 {
                                    lean_dec_ref_known(v___x_2475_, 1);
                                    v___x_2476_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2446_, v___x_2461_, v_a_2449_);
                                    return v___x_2476_;
                                } else {
                                    lean_dec(v___x_2461_);
                                    lean_dec(v_mvarId_2446_);
                                    return v___x_2475_;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_2447_);
                        lean_dec(v_mvarId_2446_);
                        v_a_2477_ = lean_ctor_get(v___x_2456_, 0);
                        v_isSharedCheck_2484_ = (!lean_is_exclusive(v___x_2456_)) as u8;
                        if v_isSharedCheck_2484_ == 0 {
                            v___x_2479_ = v___x_2456_;
                            v_isShared_2480_ = v_isSharedCheck_2484_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2477_);
                            lean_dec(v___x_2456_);
                            v___x_2479_ = lean_box(0);
                            v_isShared_2480_ = v_isSharedCheck_2484_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2480_ == 0 {
                    v___x_2482_ = v___x_2479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
                    v___x_2482_ = v_reuseFailAlloc_2483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(
    mut v_mvarId_2485_: *mut LeanObject,
    mut v_v_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
    mut v_a_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2492_: *mut LeanObject = core::ptr::null_mut();
    v_res_2492_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(
        v_mvarId_2485_,
        v_v_2486_,
        v_a_2487_,
        v_a_2488_,
        v_a_2489_,
        v_a_2490_,
    );
    lean_dec(v_a_2490_);
    lean_dec_ref(v_a_2489_);
    lean_dec(v_a_2488_);
    lean_dec_ref(v_a_2487_);
    return v_res_2492_;
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(
    mut v_mvarId_2493_: *mut LeanObject,
    mut v_val_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
    mut v___y_2496_: *mut LeanObject,
    mut v___y_2497_: *mut LeanObject,
    mut v___y_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v___x_2500_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2493_, v_val_2494_, v___y_2496_);
    return v___x_2500_;
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(
    mut v_mvarId_2501_: *mut LeanObject,
    mut v_val_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2508_: *mut LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_2501_, v_val_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
    lean_dec(v___y_2506_);
    lean_dec_ref(v___y_2505_);
    lean_dec(v___y_2504_);
    lean_dec_ref(v___y_2503_);
    return v_res_2508_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(
    mut v_00_u03b2_2509_: *mut LeanObject,
    mut v_x_2510_: *mut LeanObject,
    mut v_x_2511_: *mut LeanObject,
    mut v_x_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_2510_, v_x_2511_, v_x_2512_);
    return v___x_2513_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(
    mut v_00_u03b2_2514_: *mut LeanObject,
    mut v_x_2515_: *mut LeanObject,
    mut v_x_2516_: usize,
    mut v_x_2517_: usize,
    mut v_x_2518_: *mut LeanObject,
    mut v_x_2519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    v___x_2520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_2515_, v_x_2516_, v_x_2517_, v_x_2518_, v_x_2519_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_2521_: *mut LeanObject,
    mut v_x_2522_: *mut LeanObject,
    mut v_x_2523_: *mut LeanObject,
    mut v_x_2524_: *mut LeanObject,
    mut v_x_2525_: *mut LeanObject,
    mut v_x_2526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3561__boxed_2527_: usize = 0;
    let mut v_x_3562__boxed_2528_: usize = 0;
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
    v_x_3561__boxed_2527_ = lean_unbox_usize(v_x_2523_);
    lean_dec(v_x_2523_);
    v_x_3562__boxed_2528_ = lean_unbox_usize(v_x_2524_);
    lean_dec(v_x_2524_);
    v_res_2529_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_2521_, v_x_2522_, v_x_3561__boxed_2527_, v_x_3562__boxed_2528_, v_x_2525_, v_x_2526_);
    return v_res_2529_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2530_: *mut LeanObject,
    mut v_n_2531_: *mut LeanObject,
    mut v_k_2532_: *mut LeanObject,
    mut v_v_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    v___x_2534_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_2531_, v_k_2532_, v_v_2533_);
    return v___x_2534_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(
    mut v_00_u03b2_2535_: *mut LeanObject,
    mut v_depth_2536_: usize,
    mut v_keys_2537_: *mut LeanObject,
    mut v_vals_2538_: *mut LeanObject,
    mut v_heq_2539_: *mut LeanObject,
    mut v_i_2540_: *mut LeanObject,
    mut v_entries_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    v___x_2542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_2536_, v_keys_2537_, v_vals_2538_, v_i_2540_, v_entries_2541_);
    return v___x_2542_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_2543_: *mut LeanObject,
    mut v_depth_2544_: *mut LeanObject,
    mut v_keys_2545_: *mut LeanObject,
    mut v_vals_2546_: *mut LeanObject,
    mut v_heq_2547_: *mut LeanObject,
    mut v_i_2548_: *mut LeanObject,
    mut v_entries_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2550_: usize = 0;
    let mut v_res_2551_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2550_ = lean_unbox_usize(v_depth_2544_);
    lean_dec(v_depth_2544_);
    v_res_2551_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_2543_, v_depth_boxed_2550_, v_keys_2545_, v_vals_2546_, v_heq_2547_, v_i_2548_, v_entries_2549_);
    lean_dec_ref(v_vals_2546_);
    lean_dec_ref(v_keys_2545_);
    return v_res_2551_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(
    mut v_00_u03b2_2552_: *mut LeanObject,
    mut v_x_2553_: *mut LeanObject,
    mut v_x_2554_: *mut LeanObject,
    mut v_x_2555_: *mut LeanObject,
    mut v_x_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v___x_2557_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_2553_, v_x_2554_, v_x_2555_, v_x_2556_);
    return v___x_2557_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1()
-> *mut LeanObject {
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    v___x_2559_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0;
    v___x_2560_ = l_Lean_stringToMessageData(v___x_2559_);
    return v___x_2560_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(
    mut v_u_2561_: *mut LeanObject,
    mut v_v_x27_2562_: *mut LeanObject,
    mut v_mvarId_2563_: *mut LeanObject,
    mut v_a_2564_: *mut LeanObject,
    mut v_a_2565_: *mut LeanObject,
    mut v_a_2566_: *mut LeanObject,
    mut v_a_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2569_: u8 = 0;
    let mut v___y_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v_unused_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2585_: u8 = 0;
    let mut v_inheritedTraceOptions_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2602_: u8 = 0;
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2569_ = lean_level_eq(v_u_2561_, v_v_x27_2562_);
                if v___x_2569_ == 0 {
                    lean_dec(v_mvarId_2563_);
                    lean_dec(v_u_2561_);
                    v___x_2582_ = lean_box((v___x_2569_) as usize);
                    v___x_2583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2583_, 0, v___x_2582_);
                    return v___x_2583_;
                } else {
                    v_options_2584_ = lean_ctor_get(v_a_2566_, 2);
                    v_hasTrace_2585_ = lean_ctor_get_uint8(
                        v_options_2584_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2585_ == 0 {
                        v___y_2571_ = v_a_2565_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2586_ = lean_ctor_get(v_a_2566_, 13);
                        v_cls_2587_ =
                            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
                        v___x_2588_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
                        v___x_2589_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2586_,
                            v_options_2584_,
                            v___x_2588_,
                        );
                        if v___x_2589_ == 0 {
                            v___y_2571_ = v_a_2565_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2590_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
                            lean_inc(v_mvarId_2563_);
                            v___x_2591_ = l_Lean_mkLevelMVar(v_mvarId_2563_);
                            v___x_2592_ = l_Lean_MessageData_ofLevel(v___x_2591_);
                            v___x_2593_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2593_, 0, v___x_2590_);
                            lean_ctor_set(v___x_2593_, 1, v___x_2592_);
                            v___x_2594_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
                            v___x_2595_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2595_, 0, v___x_2593_);
                            lean_ctor_set(v___x_2595_, 1, v___x_2594_);
                            lean_inc(v_u_2561_);
                            v___x_2596_ = l_Lean_MessageData_ofLevel(v_u_2561_);
                            v___x_2597_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2597_, 0, v___x_2595_);
                            lean_ctor_set(v___x_2597_, 1, v___x_2596_);
                            v___x_2598_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_2587_, v___x_2597_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
                            if lean_obj_tag(v___x_2598_) == 0 {
                                lean_dec_ref_known(v___x_2598_, 1);
                                v___y_2571_ = v_a_2565_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_mvarId_2563_);
                                lean_dec(v_u_2561_);
                                v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
                                v_isSharedCheck_2606_ = (!lean_is_exclusive(v___x_2598_)) as u8;
                                if v_isSharedCheck_2606_ == 0 {
                                    v___x_2601_ = v___x_2598_;
                                    v_isShared_2602_ = v_isSharedCheck_2606_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2599_);
                                    lean_dec(v___x_2598_);
                                    v___x_2601_ = lean_box(0);
                                    v_isShared_2602_ = v_isSharedCheck_2606_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2572_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2563_, v_u_2561_, v___y_2571_);
                v_isSharedCheck_2580_ = (!lean_is_exclusive(v___x_2572_)) as u8;
                if v_isSharedCheck_2580_ == 0 {
                    v_unused_2581_ = lean_ctor_get(v___x_2572_, 0);
                    lean_dec(v_unused_2581_);
                    v___x_2574_ = v___x_2572_;
                    v_isShared_2575_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_2572_);
                    v___x_2574_ = lean_box(0);
                    v_isShared_2575_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2576_ = lean_box((v___x_2569_) as usize);
                if v_isShared_2575_ == 0 {
                    lean_ctor_set(v___x_2574_, 0, v___x_2576_);
                    v___x_2578_ = v___x_2574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
                    v___x_2578_ = v_reuseFailAlloc_2579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2578_;
            }
            4 => {
                if v_isShared_2602_ == 0 {
                    v___x_2604_ = v___x_2601_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
                    v___x_2604_ = v_reuseFailAlloc_2605_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(
    mut v_u_2607_: *mut LeanObject,
    mut v_v_x27_2608_: *mut LeanObject,
    mut v_mvarId_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2615_: *mut LeanObject = core::ptr::null_mut();
    v_res_2615_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(
        v_u_2607_,
        v_v_x27_2608_,
        v_mvarId_2609_,
        v_a_2610_,
        v_a_2611_,
        v_a_2612_,
        v_a_2613_,
    );
    lean_dec(v_a_2613_);
    lean_dec_ref(v_a_2612_);
    lean_dec(v_a_2611_);
    lean_dec_ref(v_a_2610_);
    lean_dec(v_v_x27_2608_);
    return v_res_2615_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(
    mut v_u_2616_: *mut LeanObject,
    mut v_v_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
    mut v_a_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2617_) == 2 {
                    v_a_2627_ = lean_ctor_get(v_v_2617_, 1);
                    lean_inc(v_a_2627_);
                    if lean_obj_tag(v_a_2627_) == 5 {
                        v_a_2628_ = lean_ctor_get(v_v_2617_, 0);
                        lean_inc(v_a_2628_);
                        lean_dec_ref_known(v_v_2617_, 2);
                        v_a_2629_ = lean_ctor_get(v_a_2627_, 0);
                        lean_inc(v_a_2629_);
                        lean_dec_ref_known(v_a_2627_, 1);
                        v___x_2630_ =
                            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(
                                v_u_2616_, v_a_2628_, v_a_2629_, v_a_2618_, v_a_2619_, v_a_2620_,
                                v_a_2621_,
                            );
                        lean_dec(v_a_2628_);
                        return v___x_2630_;
                    } else {
                        v_a_2631_ = lean_ctor_get(v_v_2617_, 0);
                        lean_inc(v_a_2631_);
                        lean_dec_ref_known(v_v_2617_, 2);
                        if lean_obj_tag(v_a_2631_) == 5 {
                            v_a_2632_ = lean_ctor_get(v_a_2631_, 0);
                            lean_inc(v_a_2632_);
                            lean_dec_ref_known(v_a_2631_, 1);
                            v___x_2633_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_2616_, v_a_2627_, v_a_2632_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
                            lean_dec(v_a_2627_);
                            return v___x_2633_;
                        } else {
                            lean_dec(v_a_2631_);
                            lean_dec(v_a_2627_);
                            lean_dec(v_u_2616_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_v_2617_);
                    lean_dec(v_u_2616_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2624_ = 0;
                v___x_2625_ = lean_box((v___x_2624_) as usize);
                v___x_2626_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2626_, 0, v___x_2625_);
                return v___x_2626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(
    mut v_u_2634_: *mut LeanObject,
    mut v_v_2635_: *mut LeanObject,
    mut v_a_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2641_: *mut LeanObject = core::ptr::null_mut();
    v_res_2641_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(
        v_u_2634_, v_v_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_,
    );
    lean_dec(v_a_2639_);
    lean_dec_ref(v_a_2638_);
    lean_dec(v_a_2637_);
    lean_dec_ref(v_a_2636_);
    return v_res_2641_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1()
-> *mut LeanObject {
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2643_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0;
    v___x_2644_ = l_Lean_stringToMessageData(v___x_2643_);
    return v___x_2644_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(
    mut v_u_u2081_2645_: *mut LeanObject,
    mut v_u_u2082_2646_: *mut LeanObject,
    mut v_v_x27_2647_: *mut LeanObject,
    mut v_mvarId_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: u8 = 0;
    let mut v___y_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2661_: u8 = 0;
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2666_: u8 = 0;
    let mut v_unused_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2673_: u8 = 0;
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut v_unused_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2684_: u8 = 0;
    let mut v_inheritedTraceOptions_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut v_options_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2707_: u8 = 0;
    let mut v_inheritedTraceOptions_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2654_ = lean_level_eq(v_u_u2081_2645_, v_v_x27_2647_);
                v___x_2655_ = 1;
                if v___x_2654_ == 0 {
                    v___x_2680_ = lean_level_eq(v_u_u2082_2646_, v_v_x27_2647_);
                    lean_dec(v_u_u2082_2646_);
                    if v___x_2680_ == 0 {
                        lean_dec(v_mvarId_2648_);
                        lean_dec(v_u_u2081_2645_);
                        v___x_2681_ = lean_box((v___x_2680_) as usize);
                        v___x_2682_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2682_, 0, v___x_2681_);
                        return v___x_2682_;
                    } else {
                        v_options_2683_ = lean_ctor_get(v_a_2651_, 2);
                        v_hasTrace_2684_ = lean_ctor_get_uint8(
                            v_options_2683_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2684_ == 0 {
                            v___y_2669_ = v_a_2650_;
                            state = 4;
                            continue;
                        } else {
                            v_inheritedTraceOptions_2685_ = lean_ctor_get(v_a_2651_, 13);
                            v_cls_2686_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
                            v___x_2687_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
                            v___x_2688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2685_,
                                v_options_2683_,
                                v___x_2687_,
                            );
                            if v___x_2688_ == 0 {
                                v___y_2669_ = v_a_2650_;
                                state = 4;
                                continue;
                            } else {
                                v___x_2689_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
                                lean_inc(v_mvarId_2648_);
                                v___x_2690_ = l_Lean_mkLevelMVar(v_mvarId_2648_);
                                v___x_2691_ = l_Lean_MessageData_ofLevel(v___x_2690_);
                                v___x_2692_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2692_, 0, v___x_2689_);
                                lean_ctor_set(v___x_2692_, 1, v___x_2691_);
                                v___x_2693_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
                                v___x_2694_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2694_, 0, v___x_2692_);
                                lean_ctor_set(v___x_2694_, 1, v___x_2693_);
                                lean_inc(v_u_u2081_2645_);
                                v___x_2695_ = l_Lean_MessageData_ofLevel(v_u_u2081_2645_);
                                v___x_2696_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2696_, 0, v___x_2694_);
                                lean_ctor_set(v___x_2696_, 1, v___x_2695_);
                                v___x_2697_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_2686_, v___x_2696_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
                                if lean_obj_tag(v___x_2697_) == 0 {
                                    lean_dec_ref_known(v___x_2697_, 1);
                                    v___y_2669_ = v_a_2650_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_dec(v_mvarId_2648_);
                                    lean_dec(v_u_u2081_2645_);
                                    v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
                                    v_isSharedCheck_2705_ = (!lean_is_exclusive(v___x_2697_)) as u8;
                                    if v_isSharedCheck_2705_ == 0 {
                                        v___x_2700_ = v___x_2697_;
                                        v_isShared_2701_ = v_isSharedCheck_2705_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2698_);
                                        lean_dec(v___x_2697_);
                                        v___x_2700_ = lean_box(0);
                                        v_isShared_2701_ = v_isSharedCheck_2705_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_u_u2081_2645_);
                    v_options_2706_ = lean_ctor_get(v_a_2651_, 2);
                    v_hasTrace_2707_ = lean_ctor_get_uint8(
                        v_options_2706_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2707_ == 0 {
                        v___y_2657_ = v_a_2650_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2708_ = lean_ctor_get(v_a_2651_, 13);
                        v_cls_2709_ =
                            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
                        v___x_2710_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
                        v___x_2711_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2708_,
                            v_options_2706_,
                            v___x_2710_,
                        );
                        if v___x_2711_ == 0 {
                            v___y_2657_ = v_a_2650_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2712_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
                            lean_inc(v_mvarId_2648_);
                            v___x_2713_ = l_Lean_mkLevelMVar(v_mvarId_2648_);
                            v___x_2714_ = l_Lean_MessageData_ofLevel(v___x_2713_);
                            v___x_2715_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2715_, 0, v___x_2712_);
                            lean_ctor_set(v___x_2715_, 1, v___x_2714_);
                            v___x_2716_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
                            v___x_2717_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2717_, 0, v___x_2715_);
                            lean_ctor_set(v___x_2717_, 1, v___x_2716_);
                            lean_inc(v_u_u2082_2646_);
                            v___x_2718_ = l_Lean_MessageData_ofLevel(v_u_u2082_2646_);
                            v___x_2719_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2719_, 0, v___x_2717_);
                            lean_ctor_set(v___x_2719_, 1, v___x_2718_);
                            v___x_2720_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_2709_, v___x_2719_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
                            if lean_obj_tag(v___x_2720_) == 0 {
                                lean_dec_ref_known(v___x_2720_, 1);
                                v___y_2657_ = v_a_2650_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_mvarId_2648_);
                                lean_dec(v_u_u2082_2646_);
                                v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
                                v_isSharedCheck_2728_ = (!lean_is_exclusive(v___x_2720_)) as u8;
                                if v_isSharedCheck_2728_ == 0 {
                                    v___x_2723_ = v___x_2720_;
                                    v_isShared_2724_ = v_isSharedCheck_2728_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2721_);
                                    lean_dec(v___x_2720_);
                                    v___x_2723_ = lean_box(0);
                                    v_isShared_2724_ = v_isSharedCheck_2728_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2658_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2648_, v_u_u2082_2646_, v___y_2657_);
                v_isSharedCheck_2666_ = (!lean_is_exclusive(v___x_2658_)) as u8;
                if v_isSharedCheck_2666_ == 0 {
                    v_unused_2667_ = lean_ctor_get(v___x_2658_, 0);
                    lean_dec(v_unused_2667_);
                    v___x_2660_ = v___x_2658_;
                    v_isShared_2661_ = v_isSharedCheck_2666_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_2658_);
                    v___x_2660_ = lean_box(0);
                    v_isShared_2661_ = v_isSharedCheck_2666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2662_ = lean_box((v___x_2655_) as usize);
                if v_isShared_2661_ == 0 {
                    lean_ctor_set(v___x_2660_, 0, v___x_2662_);
                    v___x_2664_ = v___x_2660_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
                    v___x_2664_ = v_reuseFailAlloc_2665_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2664_;
            }
            4 => {
                v___x_2670_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_2648_, v_u_u2081_2645_, v___y_2669_);
                v_isSharedCheck_2678_ = (!lean_is_exclusive(v___x_2670_)) as u8;
                if v_isSharedCheck_2678_ == 0 {
                    v_unused_2679_ = lean_ctor_get(v___x_2670_, 0);
                    lean_dec(v_unused_2679_);
                    v___x_2672_ = v___x_2670_;
                    v_isShared_2673_ = v_isSharedCheck_2678_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_2670_);
                    v___x_2672_ = lean_box(0);
                    v_isShared_2673_ = v_isSharedCheck_2678_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2674_ = lean_box((v___x_2655_) as usize);
                if v_isShared_2673_ == 0 {
                    lean_ctor_set(v___x_2672_, 0, v___x_2674_);
                    v___x_2676_ = v___x_2672_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
                    v___x_2676_ = v_reuseFailAlloc_2677_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2676_;
            }
            7 => {
                if v_isShared_2701_ == 0 {
                    v___x_2703_ = v___x_2700_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
                    v___x_2703_ = v_reuseFailAlloc_2704_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2703_;
            }
            9 => {
                if v_isShared_2724_ == 0 {
                    v___x_2726_ = v___x_2723_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(
    mut v_u_u2081_2729_: *mut LeanObject,
    mut v_u_u2082_2730_: *mut LeanObject,
    mut v_v_x27_2731_: *mut LeanObject,
    mut v_mvarId_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
    mut v_a_2734_: *mut LeanObject,
    mut v_a_2735_: *mut LeanObject,
    mut v_a_2736_: *mut LeanObject,
    mut v_a_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2738_: *mut LeanObject = core::ptr::null_mut();
    v_res_2738_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(
        v_u_u2081_2729_,
        v_u_u2082_2730_,
        v_v_x27_2731_,
        v_mvarId_2732_,
        v_a_2733_,
        v_a_2734_,
        v_a_2735_,
        v_a_2736_,
    );
    lean_dec(v_a_2736_);
    lean_dec_ref(v_a_2735_);
    lean_dec(v_a_2734_);
    lean_dec_ref(v_a_2733_);
    lean_dec(v_v_x27_2731_);
    return v_res_2738_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(
    mut v_u_2739_: *mut LeanObject,
    mut v_v_2740_: *mut LeanObject,
    mut v_a_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2747_: u8 = 0;
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_u_2739_) == 2 {
                    if lean_obj_tag(v_v_2740_) == 2 {
                        v_a_2750_ = lean_ctor_get(v_v_2740_, 1);
                        lean_inc(v_a_2750_);
                        if lean_obj_tag(v_a_2750_) == 5 {
                            v_a_2751_ = lean_ctor_get(v_u_2739_, 0);
                            lean_inc(v_a_2751_);
                            v_a_2752_ = lean_ctor_get(v_u_2739_, 1);
                            lean_inc(v_a_2752_);
                            lean_dec_ref_known(v_u_2739_, 2);
                            v_a_2753_ = lean_ctor_get(v_v_2740_, 0);
                            lean_inc(v_a_2753_);
                            lean_dec_ref_known(v_v_2740_, 2);
                            v_a_2754_ = lean_ctor_get(v_a_2750_, 0);
                            lean_inc(v_a_2754_);
                            lean_dec_ref_known(v_a_2750_, 1);
                            v___x_2755_ =
                                l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(
                                    v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2741_,
                                    v_a_2742_, v_a_2743_, v_a_2744_,
                                );
                            lean_dec(v_a_2753_);
                            return v___x_2755_;
                        } else {
                            v_a_2756_ = lean_ctor_get(v_v_2740_, 0);
                            lean_inc(v_a_2756_);
                            lean_dec_ref_known(v_v_2740_, 2);
                            if lean_obj_tag(v_a_2756_) == 5 {
                                v_a_2757_ = lean_ctor_get(v_u_2739_, 0);
                                lean_inc(v_a_2757_);
                                v_a_2758_ = lean_ctor_get(v_u_2739_, 1);
                                lean_inc(v_a_2758_);
                                lean_dec_ref_known(v_u_2739_, 2);
                                v_a_2759_ = lean_ctor_get(v_a_2756_, 0);
                                lean_inc(v_a_2759_);
                                lean_dec_ref_known(v_a_2756_, 1);
                                v___x_2760_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_2757_, v_a_2758_, v_a_2750_, v_a_2759_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
                                lean_dec(v_a_2750_);
                                return v___x_2760_;
                            } else {
                                lean_dec(v_a_2756_);
                                lean_dec(v_a_2750_);
                                lean_dec_ref_known(v_u_2739_, 2);
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_u_2739_, 2);
                        lean_dec(v_v_2740_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_v_2740_);
                    lean_dec(v_u_2739_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2747_ = 0;
                v___x_2748_ = lean_box((v___x_2747_) as usize);
                v___x_2749_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2749_, 0, v___x_2748_);
                return v___x_2749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(
    mut v_u_2761_: *mut LeanObject,
    mut v_v_2762_: *mut LeanObject,
    mut v_a_2763_: *mut LeanObject,
    mut v_a_2764_: *mut LeanObject,
    mut v_a_2765_: *mut LeanObject,
    mut v_a_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2768_: *mut LeanObject = core::ptr::null_mut();
    v_res_2768_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(
        v_u_2761_, v_v_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_,
    );
    lean_dec(v_a_2766_);
    lean_dec_ref(v_a_2765_);
    lean_dec(v_a_2764_);
    lean_dec_ref(v_a_2763_);
    return v_res_2768_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2()
-> *mut LeanObject {
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    v___x_2774_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
    v___x_2775_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9;
    v___x_2776_ = l_Lean_Name_append(v___x_2775_, v___x_2774_);
    return v___x_2776_;
}
pub unsafe fn _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4()
-> *mut LeanObject {
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    v___x_2778_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3;
    v___x_2779_ = l_Lean_stringToMessageData(v___x_2778_);
    return v___x_2779_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(
    mut v_lhs_2780_: *mut LeanObject,
    mut v_rhs_2781_: *mut LeanObject,
    mut v_a_2782_: *mut LeanObject,
    mut v_a_2783_: *mut LeanObject,
    mut v_a_2784_: *mut LeanObject,
    mut v_a_2785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v_defEqCtx_x3f_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v_hasTrace_2811_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2787_ = lean_ctor_get(v_a_2784_, 2);
                v_ref_2788_ = lean_ctor_get(v_a_2784_, 5);
                v_inheritedTraceOptions_2789_ = lean_ctor_get(v_a_2784_, 13);
                v_hasTrace_2811_ = lean_ctor_get_uint8(
                    v_options_2787_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_2811_ == 0 {
                    v___y_2791_ = v_a_2783_;
                    state = 1;
                    continue;
                } else {
                    v___x_2812_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
                    v___x_2813_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
                    v___x_2814_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2789_,
                        v_options_2787_,
                        v___x_2813_,
                    );
                    if v___x_2814_ == 0 {
                        v___y_2791_ = v_a_2783_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_lhs_2780_);
                        v___x_2815_ = l_Lean_MessageData_ofLevel(v_lhs_2780_);
                        v___x_2816_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
                        v___x_2817_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2817_, 0, v___x_2815_);
                        lean_ctor_set(v___x_2817_, 1, v___x_2816_);
                        lean_inc(v_rhs_2781_);
                        v___x_2818_ = l_Lean_MessageData_ofLevel(v_rhs_2781_);
                        v___x_2819_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2819_, 0, v___x_2817_);
                        lean_ctor_set(v___x_2819_, 1, v___x_2818_);
                        v___x_2820_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_2812_, v___x_2819_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
                        if lean_obj_tag(v___x_2820_) == 0 {
                            lean_dec_ref_known(v___x_2820_, 1);
                            v___y_2791_ = v_a_2783_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_rhs_2781_);
                            lean_dec(v_lhs_2780_);
                            return v___x_2820_;
                        }
                    }
                }
            }
            1 => {
                v___x_2792_ = lean_st_ref_take(v___y_2791_);
                v_mctx_2793_ = lean_ctor_get(v___x_2792_, 0);
                v_cache_2794_ = lean_ctor_get(v___x_2792_, 1);
                v_zetaDeltaFVarIds_2795_ = lean_ctor_get(v___x_2792_, 2);
                v_postponed_2796_ = lean_ctor_get(v___x_2792_, 3);
                v_diag_2797_ = lean_ctor_get(v___x_2792_, 4);
                v_isSharedCheck_2810_ = (!lean_is_exclusive(v___x_2792_)) as u8;
                if v_isSharedCheck_2810_ == 0 {
                    v___x_2799_ = v___x_2792_;
                    v_isShared_2800_ = v_isSharedCheck_2810_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_diag_2797_);
                    lean_inc(v_postponed_2796_);
                    lean_inc(v_zetaDeltaFVarIds_2795_);
                    lean_inc(v_cache_2794_);
                    lean_inc(v_mctx_2793_);
                    lean_dec(v___x_2792_);
                    v___x_2799_ = lean_box(0);
                    v_isShared_2800_ = v_isSharedCheck_2810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_defEqCtx_x3f_2801_ = lean_ctor_get(v_a_2782_, 4);
                lean_inc(v_defEqCtx_x3f_2801_);
                lean_inc(v_ref_2788_);
                v___x_2802_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2802_, 0, v_ref_2788_);
                lean_ctor_set(v___x_2802_, 1, v_lhs_2780_);
                lean_ctor_set(v___x_2802_, 2, v_rhs_2781_);
                lean_ctor_set(v___x_2802_, 3, v_defEqCtx_x3f_2801_);
                v___x_2803_ = l_Lean_PersistentArray_push___redArg(v_postponed_2796_, v___x_2802_);
                if v_isShared_2800_ == 0 {
                    lean_ctor_set(v___x_2799_, 3, v___x_2803_);
                    v___x_2805_ = v___x_2799_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_mctx_2793_);
                    lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_cache_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_zetaDeltaFVarIds_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2809_, 3, v___x_2803_);
                    lean_ctor_set(v_reuseFailAlloc_2809_, 4, v_diag_2797_);
                    v___x_2805_ = v_reuseFailAlloc_2809_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2806_ = lean_st_ref_set(v___y_2791_, v___x_2805_);
                v___x_2807_ = lean_box(0);
                v___x_2808_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2808_, 0, v___x_2807_);
                return v___x_2808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(
    mut v_lhs_2821_: *mut LeanObject,
    mut v_rhs_2822_: *mut LeanObject,
    mut v_a_2823_: *mut LeanObject,
    mut v_a_2824_: *mut LeanObject,
    mut v_a_2825_: *mut LeanObject,
    mut v_a_2826_: *mut LeanObject,
    mut v_a_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2828_: *mut LeanObject = core::ptr::null_mut();
    v_res_2828_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(
        v_lhs_2821_,
        v_rhs_2822_,
        v_a_2823_,
        v_a_2824_,
        v_a_2825_,
        v_a_2826_,
    );
    lean_dec(v_a_2826_);
    lean_dec_ref(v_a_2825_);
    lean_dec(v_a_2824_);
    lean_dec_ref(v_a_2823_);
    return v_res_2828_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(
    mut v_v_2829_: *mut LeanObject,
    mut v_mvarId_2830_: *mut LeanObject,
    mut v_a_2831_: *mut LeanObject,
    mut v_a_2832_: *mut LeanObject,
    mut v_a_2833_: *mut LeanObject,
    mut v_a_2834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2843_: u8 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_a_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v_a_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2861_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2829_) == 5 {
                    v_a_2836_ = lean_ctor_get(v_v_2829_, 0);
                    lean_inc(v_a_2836_);
                    lean_dec_ref_known(v_v_2829_, 1);
                    v___x_2837_ = l_Lean_LMVarId_getLevel(
                        v_a_2836_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_,
                    );
                    if lean_obj_tag(v___x_2837_) == 0 {
                        v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
                        lean_inc(v_a_2838_);
                        lean_dec_ref_known(v___x_2837_, 1);
                        v___x_2839_ = l_Lean_LMVarId_getLevel(
                            v_mvarId_2830_,
                            v_a_2831_,
                            v_a_2832_,
                            v_a_2833_,
                            v_a_2834_,
                        );
                        if lean_obj_tag(v___x_2839_) == 0 {
                            v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
                            v_isSharedCheck_2849_ = (!lean_is_exclusive(v___x_2839_)) as u8;
                            if v_isSharedCheck_2849_ == 0 {
                                v___x_2842_ = v___x_2839_;
                                v_isShared_2843_ = v_isSharedCheck_2849_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2840_);
                                lean_dec(v___x_2839_);
                                v___x_2842_ = lean_box(0);
                                v_isShared_2843_ = v_isSharedCheck_2849_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2838_);
                            v_a_2850_ = lean_ctor_get(v___x_2839_, 0);
                            v_isSharedCheck_2857_ = (!lean_is_exclusive(v___x_2839_)) as u8;
                            if v_isSharedCheck_2857_ == 0 {
                                v___x_2852_ = v___x_2839_;
                                v_isShared_2853_ = v_isSharedCheck_2857_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2850_);
                                lean_dec(v___x_2839_);
                                v___x_2852_ = lean_box(0);
                                v_isShared_2853_ = v_isSharedCheck_2857_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_mvarId_2830_);
                        v_a_2858_ = lean_ctor_get(v___x_2837_, 0);
                        v_isSharedCheck_2865_ = (!lean_is_exclusive(v___x_2837_)) as u8;
                        if v_isSharedCheck_2865_ == 0 {
                            v___x_2860_ = v___x_2837_;
                            v_isShared_2861_ = v_isSharedCheck_2865_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2858_);
                            lean_dec(v___x_2837_);
                            v___x_2860_ = lean_box(0);
                            v_isShared_2861_ = v_isSharedCheck_2865_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_2830_);
                    lean_dec(v_v_2829_);
                    v___x_2866_ = 0;
                    v___x_2867_ = lean_box((v___x_2866_) as usize);
                    v___x_2868_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2868_, 0, v___x_2867_);
                    return v___x_2868_;
                }
            }
            1 => {
                v___x_2844_ = lean_nat_dec_lt(v_a_2840_, v_a_2838_);
                lean_dec(v_a_2838_);
                lean_dec(v_a_2840_);
                v___x_2845_ = lean_box((v___x_2844_) as usize);
                if v_isShared_2843_ == 0 {
                    lean_ctor_set(v___x_2842_, 0, v___x_2845_);
                    v___x_2847_ = v___x_2842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2847_;
            }
            3 => {
                if v_isShared_2853_ == 0 {
                    v___x_2855_ = v___x_2852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
                    v___x_2855_ = v_reuseFailAlloc_2856_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2855_;
            }
            5 => {
                if v_isShared_2861_ == 0 {
                    v___x_2863_ = v___x_2860_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(
    mut v_v_2869_: *mut LeanObject,
    mut v_mvarId_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2876_: *mut LeanObject = core::ptr::null_mut();
    v_res_2876_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(
        v_v_2869_,
        v_mvarId_2870_,
        v_a_2871_,
        v_a_2872_,
        v_a_2873_,
        v_a_2874_,
    );
    lean_dec(v_a_2874_);
    lean_dec_ref(v_a_2873_);
    lean_dec(v_a_2872_);
    lean_dec_ref(v_a_2871_);
    return v_res_2876_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(
    mut v_u_2877_: *mut LeanObject,
    mut v_v_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
    mut v_a_2880_: *mut LeanObject,
    mut v_a_2881_: *mut LeanObject,
    mut v_a_2882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: u8 = 0;
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2896_: u8 = 0;
    let mut v_a_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2900_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: u8 = 0;
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2918_: u8 = 0;
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2923_: u8 = 0;
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2930_: u8 = 0;
    let mut v___x_2931_: u8 = 0;
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut v_a_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut v___x_2945_: u8 = 0;
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut v_a_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2954_: u8 = 0;
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v___y_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2965_: u8 = 0;
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_unused_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2980_: u8 = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_unused_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2992_: u8 = 0;
    let mut v___x_2993_: u8 = 0;
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: u8 = 0;
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: u8 = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v_unused_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3026_: u8 = 0;
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: u8 = 0;
    let mut v_options_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3030_: u8 = 0;
    let mut v_inheritedTraceOptions_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: u8 = 0;
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: u8 = 0;
    let mut v_options_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3052_: u8 = 0;
    let mut v_inheritedTraceOptions_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v_a_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3075_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_a_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_a_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3149_: u8 = 0;
    let mut v_a_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v_isSharedCheck_3158_: u8 = 0;
    let mut v_a_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3162_: u8 = 0;
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3166_: u8 = 0;
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u8 = 0;
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_u_2877_) {
                5 => {
                    v_a_2987_ = lean_ctor_get(v_u_2877_, 0);
                    lean_inc(v_a_2987_);
                    v___x_2988_ = l_Lean_LMVarId_isReadOnly(
                        v_a_2987_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_,
                    );
                    if lean_obj_tag(v___x_2988_) == 0 {
                        v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
                        v_isSharedCheck_3085_ = (!lean_is_exclusive(v___x_2988_)) as u8;
                        if v_isSharedCheck_3085_ == 0 {
                            v___x_2991_ = v___x_2988_;
                            v_isShared_2992_ = v_isSharedCheck_3085_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_2989_);
                            lean_dec(v___x_2988_);
                            v___x_2991_ = lean_box(0);
                            v_isShared_2992_ = v_isSharedCheck_3085_;
                            state = 23;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_u_2877_, 1);
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec(v_a_2880_);
                        lean_dec_ref(v_a_2879_);
                        lean_dec(v_v_2878_);
                        v_a_3086_ = lean_ctor_get(v___x_2988_, 0);
                        v_isSharedCheck_3093_ = (!lean_is_exclusive(v___x_2988_)) as u8;
                        if v_isSharedCheck_3093_ == 0 {
                            v___x_3088_ = v___x_2988_;
                            v_isShared_3089_ = v_isSharedCheck_3093_;
                            state = 39;
                            continue;
                        } else {
                            lean_inc(v_a_3086_);
                            lean_dec(v___x_2988_);
                            v___x_3088_ = lean_box(0);
                            v_isShared_3089_ = v_isSharedCheck_3093_;
                            state = 39;
                            continue;
                        }
                    }
                }
                0 => match lean_obj_tag(v_v_2878_) {
                    5 => {
                        lean_dec_ref_known(v_v_2878_, 1);
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec(v_a_2880_);
                        lean_dec_ref(v_a_2879_);
                        state = 6;
                        continue;
                    }
                    2 => {
                        v_a_3094_ = lean_ctor_get(v_v_2878_, 0);
                        lean_inc(v_a_3094_);
                        v_a_3095_ = lean_ctor_get(v_v_2878_, 1);
                        lean_inc(v_a_3095_);
                        lean_dec_ref_known(v_v_2878_, 2);
                        lean_inc(v_a_2882_);
                        lean_inc_ref(v_a_2881_);
                        lean_inc(v_a_2880_);
                        lean_inc_ref(v_a_2879_);
                        v___x_3096_ = lean_is_level_def_eq(
                            v_u_2877_, v_a_3094_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_,
                        );
                        if lean_obj_tag(v___x_3096_) == 0 {
                            v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
                            lean_inc(v_a_3097_);
                            v___x_3098_ = (lean_unbox(v_a_3097_) as u8);
                            lean_dec(v_a_3097_);
                            if v___x_3098_ == 0 {
                                lean_dec(v_a_3095_);
                                lean_dec(v_a_2882_);
                                lean_dec_ref(v_a_2881_);
                                lean_dec(v_a_2880_);
                                lean_dec_ref(v_a_2879_);
                                v___y_2885_ = v___x_3096_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_3096_, 1);
                                v___x_3099_ = lean_is_level_def_eq(
                                    v_u_2877_, v_a_3095_, v_a_2879_, v_a_2880_, v_a_2881_,
                                    v_a_2882_,
                                );
                                v___y_2885_ = v___x_3099_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3095_);
                            lean_dec(v_a_2882_);
                            lean_dec_ref(v_a_2881_);
                            lean_dec(v_a_2880_);
                            lean_dec_ref(v_a_2879_);
                            v___y_2885_ = v___x_3096_;
                            state = 1;
                            continue;
                        }
                    }
                    3 => {
                        v_a_3100_ = lean_ctor_get(v_v_2878_, 1);
                        lean_inc(v_a_3100_);
                        lean_dec_ref_known(v_v_2878_, 2);
                        v___x_3101_ = lean_is_level_def_eq(
                            v_u_2877_, v_a_3100_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_,
                        );
                        if lean_obj_tag(v___x_3101_) == 0 {
                            v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
                            v_isSharedCheck_3112_ = (!lean_is_exclusive(v___x_3101_)) as u8;
                            if v_isSharedCheck_3112_ == 0 {
                                v___x_3104_ = v___x_3101_;
                                v_isShared_3105_ = v_isSharedCheck_3112_;
                                state = 41;
                                continue;
                            } else {
                                lean_inc(v_a_3102_);
                                lean_dec(v___x_3101_);
                                v___x_3104_ = lean_box(0);
                                v_isShared_3105_ = v_isSharedCheck_3112_;
                                state = 41;
                                continue;
                            }
                        } else {
                            v_a_3113_ = lean_ctor_get(v___x_3101_, 0);
                            v_isSharedCheck_3120_ = (!lean_is_exclusive(v___x_3101_)) as u8;
                            if v_isSharedCheck_3120_ == 0 {
                                v___x_3115_ = v___x_3101_;
                                v_isShared_3116_ = v_isSharedCheck_3120_;
                                state = 43;
                                continue;
                            } else {
                                lean_inc(v_a_3113_);
                                lean_dec(v___x_3101_);
                                v___x_3115_ = lean_box(0);
                                v_isShared_3116_ = v_isSharedCheck_3120_;
                                state = 43;
                                continue;
                            }
                        }
                    }
                    1 => {
                        lean_dec_ref_known(v_v_2878_, 1);
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec(v_a_2880_);
                        lean_dec_ref(v_a_2879_);
                        v___x_3121_ = 0;
                        v___x_3122_ = lean_box((v___x_3121_) as usize);
                        v___x_3123_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3123_, 0, v___x_3122_);
                        return v___x_3123_;
                    }
                    _ => {
                        v___y_2914_ = v_a_2879_;
                        v___y_2915_ = v_a_2880_;
                        v___y_2916_ = v_a_2881_;
                        v___y_2917_ = v_a_2882_;
                        state = 8;
                        continue;
                    }
                },
                1 => {
                    v_a_3124_ = lean_ctor_get(v_u_2877_, 0);
                    lean_inc(v_a_3124_);
                    lean_dec_ref_known(v_u_2877_, 1);
                    if lean_obj_tag(v_v_2878_) == 5 {
                        lean_dec_ref_known(v_v_2878_, 1);
                        lean_dec(v_a_3124_);
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec(v_a_2880_);
                        lean_dec_ref(v_a_2879_);
                        state = 6;
                        continue;
                    } else {
                        v___x_3170_ = l_Lean_Level_isParam(v_v_2878_);
                        if v___x_3170_ == 0 {
                            v___x_3171_ = l_Lean_Level_isMVar(v_a_3124_);
                            if v___x_3171_ == 0 {
                                v___y_3126_ = v___x_3171_;
                                state = 45;
                                continue;
                            } else {
                                v___x_3172_ = l_Lean_Level_occurs(v_a_3124_, v_v_2878_);
                                v___y_3126_ = v___x_3172_;
                                state = 45;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3124_);
                            lean_dec(v_a_2882_);
                            lean_dec_ref(v_a_2881_);
                            lean_dec(v_a_2880_);
                            lean_dec_ref(v_a_2879_);
                            lean_dec(v_v_2878_);
                            v___x_3173_ = 0;
                            v___x_3174_ = lean_box((v___x_3173_) as usize);
                            v___x_3175_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3175_, 0, v___x_3174_);
                            return v___x_3175_;
                        }
                    }
                }
                _ => {
                    if lean_obj_tag(v_v_2878_) == 5 {
                        lean_dec_ref_known(v_v_2878_, 1);
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec(v_a_2880_);
                        lean_dec_ref(v_a_2879_);
                        lean_dec(v_u_2877_);
                        state = 6;
                        continue;
                    } else {
                        v___y_2914_ = v_a_2879_;
                        v___y_2915_ = v_a_2880_;
                        v___y_2916_ = v_a_2881_;
                        v___y_2917_ = v_a_2882_;
                        state = 8;
                        continue;
                    }
                }
            },
            1 => {
                if lean_obj_tag(v___y_2885_) == 0 {
                    v_a_2886_ = lean_ctor_get(v___y_2885_, 0);
                    v_isSharedCheck_2896_ = (!lean_is_exclusive(v___y_2885_)) as u8;
                    if v_isSharedCheck_2896_ == 0 {
                        v___x_2888_ = v___y_2885_;
                        v_isShared_2889_ = v_isSharedCheck_2896_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2886_);
                        lean_dec(v___y_2885_);
                        v___x_2888_ = lean_box(0);
                        v_isShared_2889_ = v_isSharedCheck_2896_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2897_ = lean_ctor_get(v___y_2885_, 0);
                    v_isSharedCheck_2904_ = (!lean_is_exclusive(v___y_2885_)) as u8;
                    if v_isSharedCheck_2904_ == 0 {
                        v___x_2899_ = v___y_2885_;
                        v_isShared_2900_ = v_isSharedCheck_2904_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2897_);
                        lean_dec(v___y_2885_);
                        v___x_2899_ = lean_box(0);
                        v_isShared_2900_ = v_isSharedCheck_2904_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2890_ = (lean_unbox(v_a_2886_) as u8);
                lean_dec(v_a_2886_);
                v___x_2891_ = l_Bool_toLBool(v___x_2890_);
                v___x_2892_ = lean_box((v___x_2891_) as usize);
                if v_isShared_2889_ == 0 {
                    lean_ctor_set(v___x_2888_, 0, v___x_2892_);
                    v___x_2894_ = v___x_2888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
                    v___x_2894_ = v_reuseFailAlloc_2895_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2894_;
            }
            4 => {
                if v_isShared_2900_ == 0 {
                    v___x_2902_ = v___x_2899_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
                    v___x_2902_ = v_reuseFailAlloc_2903_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2902_;
            }
            6 => {
                v___x_2906_ = 2;
                v___x_2907_ = lean_box((v___x_2906_) as usize);
                v___x_2908_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2908_, 0, v___x_2907_);
                return v___x_2908_;
            }
            7 => {
                v___x_2910_ = 2;
                v___x_2911_ = lean_box((v___x_2910_) as usize);
                v___x_2912_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2912_, 0, v___x_2911_);
                return v___x_2912_;
            }
            8 => {
                v_univApprox_2918_ = lean_ctor_get_uint8(
                    v___y_2914_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                if v_univApprox_2918_ == 0 {
                    lean_dec(v___y_2917_);
                    lean_dec_ref(v___y_2916_);
                    lean_dec(v___y_2915_);
                    lean_dec_ref(v___y_2914_);
                    lean_dec(v_v_2878_);
                    lean_dec(v_u_2877_);
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_v_2878_);
                    lean_inc(v_u_2877_);
                    v___x_2919_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(
                        v_u_2877_,
                        v_v_2878_,
                        v___y_2914_,
                        v___y_2915_,
                        v___y_2916_,
                        v___y_2917_,
                    );
                    if lean_obj_tag(v___x_2919_) == 0 {
                        v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
                        v_isSharedCheck_2950_ = (!lean_is_exclusive(v___x_2919_)) as u8;
                        if v_isSharedCheck_2950_ == 0 {
                            v___x_2922_ = v___x_2919_;
                            v_isShared_2923_ = v_isSharedCheck_2950_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2920_);
                            lean_dec(v___x_2919_);
                            v___x_2922_ = lean_box(0);
                            v_isShared_2923_ = v_isSharedCheck_2950_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v___y_2917_);
                        lean_dec_ref(v___y_2916_);
                        lean_dec(v___y_2915_);
                        lean_dec_ref(v___y_2914_);
                        lean_dec(v_v_2878_);
                        lean_dec(v_u_2877_);
                        v_a_2951_ = lean_ctor_get(v___x_2919_, 0);
                        v_isSharedCheck_2958_ = (!lean_is_exclusive(v___x_2919_)) as u8;
                        if v_isSharedCheck_2958_ == 0 {
                            v___x_2953_ = v___x_2919_;
                            v_isShared_2954_ = v_isSharedCheck_2958_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_2951_);
                            lean_dec(v___x_2919_);
                            v___x_2953_ = lean_box(0);
                            v_isShared_2954_ = v_isSharedCheck_2958_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_2924_ = (lean_unbox(v_a_2920_) as u8);
                lean_dec(v_a_2920_);
                if v___x_2924_ == 0 {
                    lean_del_object(v___x_2922_);
                    v___x_2925_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(
                        v_u_2877_,
                        v_v_2878_,
                        v___y_2914_,
                        v___y_2915_,
                        v___y_2916_,
                        v___y_2917_,
                    );
                    lean_dec(v___y_2917_);
                    lean_dec_ref(v___y_2916_);
                    lean_dec(v___y_2915_);
                    lean_dec_ref(v___y_2914_);
                    if lean_obj_tag(v___x_2925_) == 0 {
                        v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
                        v_isSharedCheck_2936_ = (!lean_is_exclusive(v___x_2925_)) as u8;
                        if v_isSharedCheck_2936_ == 0 {
                            v___x_2928_ = v___x_2925_;
                            v_isShared_2929_ = v_isSharedCheck_2936_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2926_);
                            lean_dec(v___x_2925_);
                            v___x_2928_ = lean_box(0);
                            v_isShared_2929_ = v_isSharedCheck_2936_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_2937_ = lean_ctor_get(v___x_2925_, 0);
                        v_isSharedCheck_2944_ = (!lean_is_exclusive(v___x_2925_)) as u8;
                        if v_isSharedCheck_2944_ == 0 {
                            v___x_2939_ = v___x_2925_;
                            v_isShared_2940_ = v_isSharedCheck_2944_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2937_);
                            lean_dec(v___x_2925_);
                            v___x_2939_ = lean_box(0);
                            v_isShared_2940_ = v_isSharedCheck_2944_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2917_);
                    lean_dec_ref(v___y_2916_);
                    lean_dec(v___y_2915_);
                    lean_dec_ref(v___y_2914_);
                    lean_dec(v_v_2878_);
                    lean_dec(v_u_2877_);
                    v___x_2945_ = 1;
                    v___x_2946_ = lean_box((v___x_2945_) as usize);
                    if v_isShared_2923_ == 0 {
                        lean_ctor_set(v___x_2922_, 0, v___x_2946_);
                        v___x_2948_ = v___x_2922_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
                        v___x_2948_ = v_reuseFailAlloc_2949_;
                        state = 14;
                        continue;
                    }
                }
            }
            10 => {
                v___x_2930_ = (lean_unbox(v_a_2926_) as u8);
                lean_dec(v_a_2926_);
                if v___x_2930_ == 0 {
                    lean_del_object(v___x_2928_);
                    state = 7;
                    continue;
                } else {
                    v___x_2931_ = 1;
                    v___x_2932_ = lean_box((v___x_2931_) as usize);
                    if v_isShared_2929_ == 0 {
                        lean_ctor_set(v___x_2928_, 0, v___x_2932_);
                        v___x_2934_ = v___x_2928_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
                        v___x_2934_ = v_reuseFailAlloc_2935_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_2934_;
            }
            12 => {
                if v_isShared_2940_ == 0 {
                    v___x_2942_ = v___x_2939_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
                    v___x_2942_ = v_reuseFailAlloc_2943_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2942_;
            }
            14 => {
                return v___x_2948_;
            }
            15 => {
                if v_isShared_2954_ == 0 {
                    v___x_2956_ = v___x_2953_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
                    v___x_2956_ = v_reuseFailAlloc_2957_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2956_;
            }
            17 => {
                v___x_2961_ = l_Lean_Level_mvarId_x21(v_u_2877_);
                lean_dec(v_u_2877_);
                v___x_2962_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_2961_, v_v_2878_, v___y_2960_);
                lean_dec(v___y_2960_);
                v_isSharedCheck_2971_ = (!lean_is_exclusive(v___x_2962_)) as u8;
                if v_isSharedCheck_2971_ == 0 {
                    v_unused_2972_ = lean_ctor_get(v___x_2962_, 0);
                    lean_dec(v_unused_2972_);
                    v___x_2964_ = v___x_2962_;
                    v_isShared_2965_ = v_isSharedCheck_2971_;
                    state = 18;
                    continue;
                } else {
                    lean_dec(v___x_2962_);
                    v___x_2964_ = lean_box(0);
                    v_isShared_2965_ = v_isSharedCheck_2971_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2966_ = 1;
                v___x_2967_ = lean_box((v___x_2966_) as usize);
                if v_isShared_2965_ == 0 {
                    lean_ctor_set(v___x_2964_, 0, v___x_2967_);
                    v___x_2969_ = v___x_2964_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
                    v___x_2969_ = v_reuseFailAlloc_2970_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2969_;
            }
            20 => {
                v___x_2975_ = l_Lean_Level_mvarId_x21(v_v_2878_);
                lean_dec(v_v_2878_);
                v___x_2976_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_2975_, v_u_2877_, v___y_2974_);
                lean_dec(v___y_2974_);
                v_isSharedCheck_2985_ = (!lean_is_exclusive(v___x_2976_)) as u8;
                if v_isSharedCheck_2985_ == 0 {
                    v_unused_2986_ = lean_ctor_get(v___x_2976_, 0);
                    lean_dec(v_unused_2986_);
                    v___x_2978_ = v___x_2976_;
                    v_isShared_2979_ = v_isSharedCheck_2985_;
                    state = 21;
                    continue;
                } else {
                    lean_dec(v___x_2976_);
                    v___x_2978_ = lean_box(0);
                    v_isShared_2979_ = v_isSharedCheck_2985_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2980_ = 1;
                v___x_2981_ = lean_box((v___x_2980_) as usize);
                if v_isShared_2979_ == 0 {
                    lean_ctor_set(v___x_2978_, 0, v___x_2981_);
                    v___x_2983_ = v___x_2978_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
                    v___x_2983_ = v_reuseFailAlloc_2984_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2983_;
            }
            23 => {
                v___x_2993_ = (lean_unbox(v_a_2989_) as u8);
                lean_dec(v_a_2989_);
                if v___x_2993_ == 0 {
                    lean_del_object(v___x_2991_);
                    lean_inc(v_a_2987_);
                    lean_inc(v_v_2878_);
                    v___x_2994_ =
                        l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(
                            v_v_2878_, v_a_2987_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_,
                        );
                    if lean_obj_tag(v___x_2994_) == 0 {
                        v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
                        v_isSharedCheck_3071_ = (!lean_is_exclusive(v___x_2994_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_2997_ = v___x_2994_;
                            v_isShared_2998_ = v_isSharedCheck_3071_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_2995_);
                            lean_dec(v___x_2994_);
                            v___x_2997_ = lean_box(0);
                            v_isShared_2998_ = v_isSharedCheck_3071_;
                            state = 24;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_u_2877_, 1);
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec(v_a_2880_);
                        lean_dec_ref(v_a_2879_);
                        lean_dec(v_v_2878_);
                        v_a_3072_ = lean_ctor_get(v___x_2994_, 0);
                        v_isSharedCheck_3079_ = (!lean_is_exclusive(v___x_2994_)) as u8;
                        if v_isSharedCheck_3079_ == 0 {
                            v___x_3074_ = v___x_2994_;
                            v_isShared_3075_ = v_isSharedCheck_3079_;
                            state = 36;
                            continue;
                        } else {
                            lean_inc(v_a_3072_);
                            lean_dec(v___x_2994_);
                            v___x_3074_ = lean_box(0);
                            v_isShared_3075_ = v_isSharedCheck_3079_;
                            state = 36;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_u_2877_, 1);
                    lean_dec(v_a_2882_);
                    lean_dec_ref(v_a_2881_);
                    lean_dec(v_a_2880_);
                    lean_dec_ref(v_a_2879_);
                    lean_dec(v_v_2878_);
                    v___x_3080_ = 2;
                    v___x_3081_ = lean_box((v___x_3080_) as usize);
                    if v_isShared_2992_ == 0 {
                        lean_ctor_set(v___x_2991_, 0, v___x_3081_);
                        v___x_3083_ = v___x_2991_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
                        v___x_3083_ = v_reuseFailAlloc_3084_;
                        state = 38;
                        continue;
                    }
                }
            }
            24 => {
                v___x_3027_ = (lean_unbox(v_a_2995_) as u8);
                lean_dec(v_a_2995_);
                if v___x_3027_ == 0 {
                    v___x_3028_ = l_Lean_Level_occurs(v_u_2877_, v_v_2878_);
                    if v___x_3028_ == 0 {
                        lean_del_object(v___x_2997_);
                        v_options_3029_ = lean_ctor_get(v_a_2881_, 2);
                        v_hasTrace_3030_ = lean_ctor_get_uint8(
                            v_options_3029_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3030_ == 0 {
                            lean_dec(v_a_2882_);
                            lean_dec_ref(v_a_2881_);
                            lean_dec_ref(v_a_2879_);
                            v___y_2960_ = v_a_2880_;
                            state = 17;
                            continue;
                        } else {
                            v_inheritedTraceOptions_3031_ = lean_ctor_get(v_a_2881_, 13);
                            v___x_3032_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
                            v___x_3033_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
                            v___x_3034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3031_,
                                v_options_3029_,
                                v___x_3033_,
                            );
                            if v___x_3034_ == 0 {
                                lean_dec(v_a_2882_);
                                lean_dec_ref(v_a_2881_);
                                lean_dec_ref(v_a_2879_);
                                v___y_2960_ = v_a_2880_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc_ref(v_u_2877_);
                                v___x_3035_ = l_Lean_MessageData_ofLevel(v_u_2877_);
                                v___x_3036_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
                                v___x_3037_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3037_, 0, v___x_3035_);
                                lean_ctor_set(v___x_3037_, 1, v___x_3036_);
                                lean_inc(v_v_2878_);
                                v___x_3038_ = l_Lean_MessageData_ofLevel(v_v_2878_);
                                v___x_3039_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3039_, 0, v___x_3037_);
                                lean_ctor_set(v___x_3039_, 1, v___x_3038_);
                                v___x_3040_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_3032_, v___x_3039_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
                                lean_dec(v_a_2882_);
                                lean_dec_ref(v_a_2881_);
                                lean_dec_ref(v_a_2879_);
                                if lean_obj_tag(v___x_3040_) == 0 {
                                    lean_dec_ref_known(v___x_3040_, 1);
                                    v___y_2960_ = v_a_2880_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v_u_2877_, 1);
                                    lean_dec(v_a_2880_);
                                    lean_dec(v_v_2878_);
                                    v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
                                    v_isSharedCheck_3048_ = (!lean_is_exclusive(v___x_3040_)) as u8;
                                    if v_isSharedCheck_3048_ == 0 {
                                        v___x_3043_ = v___x_3040_;
                                        v_isShared_3044_ = v_isSharedCheck_3048_;
                                        state = 32;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3041_);
                                        lean_dec(v___x_3040_);
                                        v___x_3043_ = lean_box(0);
                                        v_isShared_3044_ = v_isSharedCheck_3048_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v___x_3049_ = l_Lean_Level_isMax(v_v_2878_);
                        if v___x_3049_ == 0 {
                            v___y_3006_ = v___x_3049_;
                            state = 27;
                            continue;
                        } else {
                            v___x_3050_ =
                                l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(
                                    v_u_2877_, v_v_2878_,
                                );
                            if v___x_3050_ == 0 {
                                v___y_3006_ = v___x_3049_;
                                state = 27;
                                continue;
                            } else {
                                lean_dec_ref_known(v_u_2877_, 1);
                                lean_dec(v_a_2882_);
                                lean_dec_ref(v_a_2881_);
                                lean_dec(v_a_2880_);
                                lean_dec_ref(v_a_2879_);
                                lean_dec(v_v_2878_);
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_2997_);
                    v_options_3051_ = lean_ctor_get(v_a_2881_, 2);
                    v_hasTrace_3052_ = lean_ctor_get_uint8(
                        v_options_3051_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3052_ == 0 {
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec_ref(v_a_2879_);
                        v___y_2974_ = v_a_2880_;
                        state = 20;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3053_ = lean_ctor_get(v_a_2881_, 13);
                        v___x_3054_ =
                            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7;
                        v___x_3055_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
                        v___x_3056_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3053_,
                            v_options_3051_,
                            v___x_3055_,
                        );
                        if v___x_3056_ == 0 {
                            lean_dec(v_a_2882_);
                            lean_dec_ref(v_a_2881_);
                            lean_dec_ref(v_a_2879_);
                            v___y_2974_ = v_a_2880_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_v_2878_);
                            v___x_3057_ = l_Lean_MessageData_ofLevel(v_v_2878_);
                            v___x_3058_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
                            v___x_3059_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3059_, 0, v___x_3057_);
                            lean_ctor_set(v___x_3059_, 1, v___x_3058_);
                            lean_inc_ref(v_u_2877_);
                            v___x_3060_ = l_Lean_MessageData_ofLevel(v_u_2877_);
                            v___x_3061_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3061_, 0, v___x_3059_);
                            lean_ctor_set(v___x_3061_, 1, v___x_3060_);
                            v___x_3062_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_3054_, v___x_3061_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
                            lean_dec(v_a_2882_);
                            lean_dec_ref(v_a_2881_);
                            lean_dec_ref(v_a_2879_);
                            if lean_obj_tag(v___x_3062_) == 0 {
                                lean_dec_ref_known(v___x_3062_, 1);
                                v___y_2974_ = v_a_2880_;
                                state = 20;
                                continue;
                            } else {
                                lean_dec_ref_known(v_u_2877_, 1);
                                lean_dec(v_a_2880_);
                                lean_dec(v_v_2878_);
                                v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
                                v_isSharedCheck_3070_ = (!lean_is_exclusive(v___x_3062_)) as u8;
                                if v_isSharedCheck_3070_ == 0 {
                                    v___x_3065_ = v___x_3062_;
                                    v_isShared_3066_ = v_isSharedCheck_3070_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_a_3063_);
                                    lean_dec(v___x_3062_);
                                    v___x_3065_ = lean_box(0);
                                    v_isShared_3066_ = v_isSharedCheck_3070_;
                                    state = 34;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            25 => {
                v___x_3000_ = 2;
                v___x_3001_ = lean_box((v___x_3000_) as usize);
                if v_isShared_2998_ == 0 {
                    lean_ctor_set(v___x_2997_, 0, v___x_3001_);
                    v___x_3003_ = v___x_2997_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3003_;
            }
            27 => {
                if v___y_3006_ == 0 {
                    lean_dec_ref_known(v_u_2877_, 1);
                    lean_dec(v_a_2882_);
                    lean_dec_ref(v_a_2881_);
                    lean_dec(v_a_2880_);
                    lean_dec_ref(v_a_2879_);
                    lean_dec(v_v_2878_);
                    state = 25;
                    continue;
                } else {
                    lean_del_object(v___x_2997_);
                    v___x_3007_ = l_Lean_Level_mvarId_x21(v_u_2877_);
                    lean_dec_ref_known(v_u_2877_, 1);
                    v___x_3008_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(
                        v___x_3007_,
                        v_v_2878_,
                        v_a_2879_,
                        v_a_2880_,
                        v_a_2881_,
                        v_a_2882_,
                    );
                    lean_dec(v_a_2882_);
                    lean_dec_ref(v_a_2881_);
                    lean_dec(v_a_2880_);
                    lean_dec_ref(v_a_2879_);
                    if lean_obj_tag(v___x_3008_) == 0 {
                        v_isSharedCheck_3017_ = (!lean_is_exclusive(v___x_3008_)) as u8;
                        if v_isSharedCheck_3017_ == 0 {
                            v_unused_3018_ = lean_ctor_get(v___x_3008_, 0);
                            lean_dec(v_unused_3018_);
                            v___x_3010_ = v___x_3008_;
                            v_isShared_3011_ = v_isSharedCheck_3017_;
                            state = 28;
                            continue;
                        } else {
                            lean_dec(v___x_3008_);
                            v___x_3010_ = lean_box(0);
                            v_isShared_3011_ = v_isSharedCheck_3017_;
                            state = 28;
                            continue;
                        }
                    } else {
                        v_a_3019_ = lean_ctor_get(v___x_3008_, 0);
                        v_isSharedCheck_3026_ = (!lean_is_exclusive(v___x_3008_)) as u8;
                        if v_isSharedCheck_3026_ == 0 {
                            v___x_3021_ = v___x_3008_;
                            v_isShared_3022_ = v_isSharedCheck_3026_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_3019_);
                            lean_dec(v___x_3008_);
                            v___x_3021_ = lean_box(0);
                            v_isShared_3022_ = v_isSharedCheck_3026_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            28 => {
                v___x_3012_ = 1;
                v___x_3013_ = lean_box((v___x_3012_) as usize);
                if v_isShared_3011_ == 0 {
                    lean_ctor_set(v___x_3010_, 0, v___x_3013_);
                    v___x_3015_ = v___x_3010_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
                    v___x_3015_ = v_reuseFailAlloc_3016_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3015_;
            }
            30 => {
                if v_isShared_3022_ == 0 {
                    v___x_3024_ = v___x_3021_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
                    v___x_3024_ = v_reuseFailAlloc_3025_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3024_;
            }
            32 => {
                if v_isShared_3044_ == 0 {
                    v___x_3046_ = v___x_3043_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
                    v___x_3046_ = v_reuseFailAlloc_3047_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3046_;
            }
            34 => {
                if v_isShared_3066_ == 0 {
                    v___x_3068_ = v___x_3065_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
                    v___x_3068_ = v_reuseFailAlloc_3069_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3068_;
            }
            36 => {
                if v_isShared_3075_ == 0 {
                    v___x_3077_ = v___x_3074_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
                    v___x_3077_ = v_reuseFailAlloc_3078_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3077_;
            }
            38 => {
                return v___x_3083_;
            }
            39 => {
                if v_isShared_3089_ == 0 {
                    v___x_3091_ = v___x_3088_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
                    v___x_3091_ = v_reuseFailAlloc_3092_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3091_;
            }
            41 => {
                v___x_3106_ = (lean_unbox(v_a_3102_) as u8);
                lean_dec(v_a_3102_);
                v___x_3107_ = l_Bool_toLBool(v___x_3106_);
                v___x_3108_ = lean_box((v___x_3107_) as usize);
                if v_isShared_3105_ == 0 {
                    lean_ctor_set(v___x_3104_, 0, v___x_3108_);
                    v___x_3110_ = v___x_3104_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
                    v___x_3110_ = v_reuseFailAlloc_3111_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3110_;
            }
            43 => {
                if v_isShared_3116_ == 0 {
                    v___x_3118_ = v___x_3115_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
                    v___x_3118_ = v_reuseFailAlloc_3119_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_3118_;
            }
            45 => {
                if v___y_3126_ == 0 {
                    v___x_3127_ = l_Lean_Meta_decLevel_x3f(
                        v_v_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_,
                    );
                    if lean_obj_tag(v___x_3127_) == 0 {
                        v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
                        v_isSharedCheck_3158_ = (!lean_is_exclusive(v___x_3127_)) as u8;
                        if v_isSharedCheck_3158_ == 0 {
                            v___x_3130_ = v___x_3127_;
                            v_isShared_3131_ = v_isSharedCheck_3158_;
                            state = 46;
                            continue;
                        } else {
                            lean_inc(v_a_3128_);
                            lean_dec(v___x_3127_);
                            v___x_3130_ = lean_box(0);
                            v_isShared_3131_ = v_isSharedCheck_3158_;
                            state = 46;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3124_);
                        lean_dec(v_a_2882_);
                        lean_dec_ref(v_a_2881_);
                        lean_dec(v_a_2880_);
                        lean_dec_ref(v_a_2879_);
                        v_a_3159_ = lean_ctor_get(v___x_3127_, 0);
                        v_isSharedCheck_3166_ = (!lean_is_exclusive(v___x_3127_)) as u8;
                        if v_isSharedCheck_3166_ == 0 {
                            v___x_3161_ = v___x_3127_;
                            v_isShared_3162_ = v_isSharedCheck_3166_;
                            state = 52;
                            continue;
                        } else {
                            lean_inc(v_a_3159_);
                            lean_dec(v___x_3127_);
                            v___x_3161_ = lean_box(0);
                            v_isShared_3162_ = v_isSharedCheck_3166_;
                            state = 52;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3124_);
                    lean_dec(v_a_2882_);
                    lean_dec_ref(v_a_2881_);
                    lean_dec(v_a_2880_);
                    lean_dec_ref(v_a_2879_);
                    lean_dec(v_v_2878_);
                    v___x_3167_ = 2;
                    v___x_3168_ = lean_box((v___x_3167_) as usize);
                    v___x_3169_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3169_, 0, v___x_3168_);
                    return v___x_3169_;
                }
            }
            46 => {
                if lean_obj_tag(v_a_3128_) == 0 {
                    lean_dec(v_a_3124_);
                    lean_dec(v_a_2882_);
                    lean_dec_ref(v_a_2881_);
                    lean_dec(v_a_2880_);
                    lean_dec_ref(v_a_2879_);
                    v___x_3132_ = 2;
                    v___x_3133_ = lean_box((v___x_3132_) as usize);
                    if v_isShared_3131_ == 0 {
                        lean_ctor_set(v___x_3130_, 0, v___x_3133_);
                        v___x_3135_ = v___x_3130_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
                        v___x_3135_ = v_reuseFailAlloc_3136_;
                        state = 47;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3130_);
                    v_val_3137_ = lean_ctor_get(v_a_3128_, 0);
                    lean_inc(v_val_3137_);
                    lean_dec_ref_known(v_a_3128_, 1);
                    v___x_3138_ = lean_is_level_def_eq(
                        v_a_3124_,
                        v_val_3137_,
                        v_a_2879_,
                        v_a_2880_,
                        v_a_2881_,
                        v_a_2882_,
                    );
                    if lean_obj_tag(v___x_3138_) == 0 {
                        v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
                        v_isSharedCheck_3149_ = (!lean_is_exclusive(v___x_3138_)) as u8;
                        if v_isSharedCheck_3149_ == 0 {
                            v___x_3141_ = v___x_3138_;
                            v_isShared_3142_ = v_isSharedCheck_3149_;
                            state = 48;
                            continue;
                        } else {
                            lean_inc(v_a_3139_);
                            lean_dec(v___x_3138_);
                            v___x_3141_ = lean_box(0);
                            v_isShared_3142_ = v_isSharedCheck_3149_;
                            state = 48;
                            continue;
                        }
                    } else {
                        v_a_3150_ = lean_ctor_get(v___x_3138_, 0);
                        v_isSharedCheck_3157_ = (!lean_is_exclusive(v___x_3138_)) as u8;
                        if v_isSharedCheck_3157_ == 0 {
                            v___x_3152_ = v___x_3138_;
                            v_isShared_3153_ = v_isSharedCheck_3157_;
                            state = 50;
                            continue;
                        } else {
                            lean_inc(v_a_3150_);
                            lean_dec(v___x_3138_);
                            v___x_3152_ = lean_box(0);
                            v_isShared_3153_ = v_isSharedCheck_3157_;
                            state = 50;
                            continue;
                        }
                    }
                }
            }
            47 => {
                return v___x_3135_;
            }
            48 => {
                v___x_3143_ = (lean_unbox(v_a_3139_) as u8);
                lean_dec(v_a_3139_);
                v___x_3144_ = l_Bool_toLBool(v___x_3143_);
                v___x_3145_ = lean_box((v___x_3144_) as usize);
                if v_isShared_3142_ == 0 {
                    lean_ctor_set(v___x_3141_, 0, v___x_3145_);
                    v___x_3147_ = v___x_3141_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
                    v___x_3147_ = v_reuseFailAlloc_3148_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_3147_;
            }
            50 => {
                if v_isShared_3153_ == 0 {
                    v___x_3155_ = v___x_3152_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
                    v___x_3155_ = v_reuseFailAlloc_3156_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_3155_;
            }
            52 => {
                if v_isShared_3162_ == 0 {
                    v___x_3164_ = v___x_3161_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
                    v___x_3164_ = v_reuseFailAlloc_3165_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_3164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(
    mut v_u_3176_: *mut LeanObject,
    mut v_v_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
    mut v_a_3179_: *mut LeanObject,
    mut v_a_3180_: *mut LeanObject,
    mut v_a_3181_: *mut LeanObject,
    mut v_a_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3183_: *mut LeanObject = core::ptr::null_mut();
    v_res_3183_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(
        v_u_3176_, v_v_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_,
    );
    return v_res_3183_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(
    mut v_l_3184_: *mut LeanObject,
    mut v___y_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3199_: u8 = 0;
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_unused_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3187_ = lean_st_ref_get(v___y_3185_);
                v_mctx_3188_ = lean_ctor_get(v___x_3187_, 0);
                lean_inc_ref(v_mctx_3188_);
                lean_dec(v___x_3187_);
                v___x_3189_ = lean_instantiate_level_mvars(v_mctx_3188_, v_l_3184_);
                v_fst_3190_ = lean_ctor_get(v___x_3189_, 0);
                lean_inc(v_fst_3190_);
                v_snd_3191_ = lean_ctor_get(v___x_3189_, 1);
                lean_inc(v_snd_3191_);
                lean_dec_ref(v___x_3189_);
                v___x_3192_ = lean_st_ref_take(v___y_3185_);
                v_cache_3193_ = lean_ctor_get(v___x_3192_, 1);
                v_zetaDeltaFVarIds_3194_ = lean_ctor_get(v___x_3192_, 2);
                v_postponed_3195_ = lean_ctor_get(v___x_3192_, 3);
                v_diag_3196_ = lean_ctor_get(v___x_3192_, 4);
                v_isSharedCheck_3205_ = (!lean_is_exclusive(v___x_3192_)) as u8;
                if v_isSharedCheck_3205_ == 0 {
                    v_unused_3206_ = lean_ctor_get(v___x_3192_, 0);
                    lean_dec(v_unused_3206_);
                    v___x_3198_ = v___x_3192_;
                    v_isShared_3199_ = v_isSharedCheck_3205_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3196_);
                    lean_inc(v_postponed_3195_);
                    lean_inc(v_zetaDeltaFVarIds_3194_);
                    lean_inc(v_cache_3193_);
                    lean_dec(v___x_3192_);
                    v___x_3198_ = lean_box(0);
                    v_isShared_3199_ = v_isSharedCheck_3205_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3199_ == 0 {
                    lean_ctor_set(v___x_3198_, 0, v_fst_3190_);
                    v___x_3201_ = v___x_3198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_fst_3190_);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_cache_3193_);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 2, v_zetaDeltaFVarIds_3194_);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 3, v_postponed_3195_);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 4, v_diag_3196_);
                    v___x_3201_ = v_reuseFailAlloc_3204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3202_ = lean_st_ref_set(v___y_3185_, v___x_3201_);
                v___x_3203_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3203_, 0, v_snd_3191_);
                return v___x_3203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(
    mut v_l_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3210_: *mut LeanObject = core::ptr::null_mut();
    v_res_3210_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(
            v_l_3207_,
            v___y_3208_,
        );
    lean_dec(v___y_3208_);
    return v_res_3210_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(
    mut v_l_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
    mut v___y_3215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    v___x_3217_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(
            v_l_3211_,
            v___y_3213_,
        );
    return v___x_3217_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(
    mut v_l_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3224_: *mut LeanObject = core::ptr::null_mut();
    v_res_3224_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(
        v_l_3218_,
        v___y_3219_,
        v___y_3220_,
        v___y_3221_,
        v___y_3222_,
    );
    lean_dec(v___y_3222_);
    lean_dec_ref(v___y_3221_);
    lean_dec(v___y_3220_);
    lean_dec_ref(v___y_3219_);
    return v_res_3224_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    v___x_3225_ = lean_unsigned_to_nat(32);
    v___x_3226_ = lean_mk_empty_array_with_capacity(v___x_3225_);
    v___x_3227_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3227_, 0, v___x_3226_);
    return v___x_3227_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3228_: usize = 0;
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    v___x_3228_ = 5usize;
    v___x_3229_ = lean_unsigned_to_nat(0);
    v___x_3230_ = lean_unsigned_to_nat(32);
    v___x_3231_ = lean_mk_empty_array_with_capacity(v___x_3230_);
    v___x_3232_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
    v___x_3233_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3233_, 0, v___x_3232_);
    lean_ctor_set(v___x_3233_, 1, v___x_3231_);
    lean_ctor_set(v___x_3233_, 2, v___x_3229_);
    lean_ctor_set(v___x_3233_, 3, v___x_3229_);
    lean_ctor_set_usize(v___x_3233_, 4, v___x_3228_);
    return v___x_3233_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(
    mut v___y_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v_tid_3252_: u64 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_unused_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3236_ = lean_st_ref_get(v___y_3234_);
                v_traceState_3237_ = lean_ctor_get(v___x_3236_, 4);
                lean_inc_ref(v_traceState_3237_);
                lean_dec(v___x_3236_);
                v_traces_3238_ = lean_ctor_get(v_traceState_3237_, 0);
                lean_inc_ref(v_traces_3238_);
                lean_dec_ref(v_traceState_3237_);
                v___x_3239_ = lean_st_ref_take(v___y_3234_);
                v_traceState_3240_ = lean_ctor_get(v___x_3239_, 4);
                v_env_3241_ = lean_ctor_get(v___x_3239_, 0);
                v_nextMacroScope_3242_ = lean_ctor_get(v___x_3239_, 1);
                v_ngen_3243_ = lean_ctor_get(v___x_3239_, 2);
                v_auxDeclNGen_3244_ = lean_ctor_get(v___x_3239_, 3);
                v_cache_3245_ = lean_ctor_get(v___x_3239_, 5);
                v_messages_3246_ = lean_ctor_get(v___x_3239_, 6);
                v_infoState_3247_ = lean_ctor_get(v___x_3239_, 7);
                v_snapshotTasks_3248_ = lean_ctor_get(v___x_3239_, 8);
                v_isSharedCheck_3267_ = (!lean_is_exclusive(v___x_3239_)) as u8;
                if v_isSharedCheck_3267_ == 0 {
                    v___x_3250_ = v___x_3239_;
                    v_isShared_3251_ = v_isSharedCheck_3267_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3248_);
                    lean_inc(v_infoState_3247_);
                    lean_inc(v_messages_3246_);
                    lean_inc(v_cache_3245_);
                    lean_inc(v_traceState_3240_);
                    lean_inc(v_auxDeclNGen_3244_);
                    lean_inc(v_ngen_3243_);
                    lean_inc(v_nextMacroScope_3242_);
                    lean_inc(v_env_3241_);
                    lean_dec(v___x_3239_);
                    v___x_3250_ = lean_box(0);
                    v_isShared_3251_ = v_isSharedCheck_3267_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_3252_ = lean_ctor_get_uint64(
                    v_traceState_3240_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3265_ = (!lean_is_exclusive(v_traceState_3240_)) as u8;
                if v_isSharedCheck_3265_ == 0 {
                    v_unused_3266_ = lean_ctor_get(v_traceState_3240_, 0);
                    lean_dec(v_unused_3266_);
                    v___x_3254_ = v_traceState_3240_;
                    v_isShared_3255_ = v_isSharedCheck_3265_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_traceState_3240_);
                    v___x_3254_ = lean_box(0);
                    v_isShared_3255_ = v_isSharedCheck_3265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3256_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
                if v_isShared_3255_ == 0 {
                    lean_ctor_set(v___x_3254_, 0, v___x_3256_);
                    v___x_3258_ = v___x_3254_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3256_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3264_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3252_,
                    );
                    v___x_3258_ = v_reuseFailAlloc_3264_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3251_ == 0 {
                    lean_ctor_set(v___x_3250_, 4, v___x_3258_);
                    v___x_3260_ = v___x_3250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_env_3241_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_nextMacroScope_3242_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_ngen_3243_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_auxDeclNGen_3244_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 4, v___x_3258_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 5, v_cache_3245_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 6, v_messages_3246_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 7, v_infoState_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 8, v_snapshotTasks_3248_);
                    v___x_3260_ = v_reuseFailAlloc_3263_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3261_ = lean_st_ref_set(v___y_3234_, v___x_3260_);
                v___x_3262_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3262_, 0, v_traces_3238_);
                return v___x_3262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3270_: *mut LeanObject = core::ptr::null_mut();
    v_res_3270_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_3268_);
    lean_dec(v___y_3268_);
    return v_res_3270_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(
    mut v___y_3271_: *mut LeanObject,
    mut v___y_3272_: *mut LeanObject,
    mut v___y_3273_: *mut LeanObject,
    mut v___y_3274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    v___x_3276_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_3274_);
    return v___x_3276_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(
    mut v___y_3277_: *mut LeanObject,
    mut v___y_3278_: *mut LeanObject,
    mut v___y_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3282_: *mut LeanObject = core::ptr::null_mut();
    v_res_3282_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
    lean_dec(v___y_3280_);
    lean_dec_ref(v___y_3279_);
    lean_dec(v___y_3278_);
    lean_dec_ref(v___y_3277_);
    return v_res_3282_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(
    mut v_o_3283_: *mut LeanObject,
    mut v_k_3284_: *mut LeanObject,
    mut v_v_3285_: u8,
) -> *mut LeanObject {
    let mut v_map_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3287_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: u8 = 0;
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3286_ = lean_ctor_get(v_o_3283_, 0);
                v_hasTrace_3287_ = lean_ctor_get_uint8(
                    v_o_3283_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3301_ = (!lean_is_exclusive(v_o_3283_)) as u8;
                if v_isSharedCheck_3301_ == 0 {
                    v___x_3289_ = v_o_3283_;
                    v_isShared_3290_ = v_isSharedCheck_3301_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_3286_);
                    lean_dec(v_o_3283_);
                    v___x_3289_ = lean_box(0);
                    v_isShared_3290_ = v_isSharedCheck_3301_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3291_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_3291_, 0 as u32, v_v_3285_);
                lean_inc(v_k_3284_);
                v___x_3292_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3284_, v___x_3291_, v_map_3286_);
                if v_hasTrace_3287_ == 0 {
                    v___x_3293_ =
                        l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9;
                    v___x_3294_ = l_Lean_Name_isPrefixOf(v___x_3293_, v_k_3284_);
                    lean_dec(v_k_3284_);
                    if v_isShared_3290_ == 0 {
                        lean_ctor_set(v___x_3289_, 0, v___x_3292_);
                        v___x_3296_ = v___x_3289_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3292_);
                        v___x_3296_ = v_reuseFailAlloc_3297_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_3284_);
                    if v_isShared_3290_ == 0 {
                        lean_ctor_set(v___x_3289_, 0, v___x_3292_);
                        v___x_3299_ = v___x_3289_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3292_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_3300_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_3287_,
                        );
                        v___x_3299_ = v_reuseFailAlloc_3300_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3296_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3294_,
                );
                return v___x_3296_;
            }
            3 => {
                return v___x_3299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(
    mut v_o_3302_: *mut LeanObject,
    mut v_k_3303_: *mut LeanObject,
    mut v_v_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_3305_: u8 = 0;
    let mut v_res_3306_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_3305_ = (lean_unbox(v_v_3304_) as u8);
    v_res_3306_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(
        v_o_3302_,
        v_k_3303_,
        v_v_boxed_3305_,
    );
    return v_res_3306_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(
    mut v_opts_3307_: *mut LeanObject,
    mut v_opt_3308_: *mut LeanObject,
) -> u8 {
    let mut v_name_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    v_name_3309_ = lean_ctor_get(v_opt_3308_, 0);
    v_defValue_3310_ = lean_ctor_get(v_opt_3308_, 1);
    v_map_3311_ = lean_ctor_get(v_opts_3307_, 0);
    v___x_3312_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3311_,
            v_name_3309_,
        );
    if lean_obj_tag(v___x_3312_) == 0 {
        let mut v___x_3313_: u8 = 0;
        v___x_3313_ = (lean_unbox(v_defValue_3310_) as u8);
        return v___x_3313_;
    } else {
        let mut v_val_3314_: *mut LeanObject = core::ptr::null_mut();
        v_val_3314_ = lean_ctor_get(v___x_3312_, 0);
        lean_inc(v_val_3314_);
        lean_dec_ref_known(v___x_3312_, 1);
        if lean_obj_tag(v_val_3314_) == 1 {
            let mut v_v_3315_: u8 = 0;
            v_v_3315_ = lean_ctor_get_uint8(v_val_3314_, 0 as u32);
            lean_dec_ref_known(v_val_3314_, 0);
            return v_v_3315_;
        } else {
            let mut v___x_3316_: u8 = 0;
            lean_dec(v_val_3314_);
            v___x_3316_ = (lean_unbox(v_defValue_3310_) as u8);
            return v___x_3316_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(
    mut v_opts_3317_: *mut LeanObject,
    mut v_opt_3318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3319_: u8 = 0;
    let mut v_r_3320_: *mut LeanObject = core::ptr::null_mut();
    v_res_3319_ =
        l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_3317_, v_opt_3318_);
    lean_dec_ref(v_opt_3318_);
    lean_dec_ref(v_opts_3317_);
    v_r_3320_ = lean_box((v_res_3319_) as usize);
    return v_r_3320_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(
    mut v_opts_3321_: *mut LeanObject,
    mut v_opt_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    v_name_3323_ = lean_ctor_get(v_opt_3322_, 0);
    v_defValue_3324_ = lean_ctor_get(v_opt_3322_, 1);
    v_map_3325_ = lean_ctor_get(v_opts_3321_, 0);
    v___x_3326_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3325_,
            v_name_3323_,
        );
    if lean_obj_tag(v___x_3326_) == 0 {
        lean_inc(v_defValue_3324_);
        return v_defValue_3324_;
    } else {
        let mut v_val_3327_: *mut LeanObject = core::ptr::null_mut();
        v_val_3327_ = lean_ctor_get(v___x_3326_, 0);
        lean_inc(v_val_3327_);
        lean_dec_ref_known(v___x_3326_, 1);
        if lean_obj_tag(v_val_3327_) == 3 {
            let mut v_v_3328_: *mut LeanObject = core::ptr::null_mut();
            v_v_3328_ = lean_ctor_get(v_val_3327_, 0);
            lean_inc(v_v_3328_);
            lean_dec_ref_known(v_val_3327_, 1);
            return v_v_3328_;
        } else {
            lean_dec(v_val_3327_);
            lean_inc(v_defValue_3324_);
            return v_defValue_3324_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(
    mut v_opts_3329_: *mut LeanObject,
    mut v_opt_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3331_: *mut LeanObject = core::ptr::null_mut();
    v_res_3331_ =
        l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_3329_, v_opt_3330_);
    lean_dec_ref(v_opt_3330_);
    lean_dec_ref(v_opts_3329_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(
    mut v___x_3332_: u8,
    mut v_lhs_3333_: *mut LeanObject,
    mut v_rhs_3334_: *mut LeanObject,
    mut v___x_3335_: *mut LeanObject,
    mut v___x_3336_: *mut LeanObject,
    mut v___x_3337_: u8,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3345_: u8 = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3364_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v___y_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDefEqStuckEx_3377_: u8 = 0;
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: u8 = 0;
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3391_: u8 = 0;
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v_unused_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut v_isSharedCheck_3406_: u8 = 0;
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: u8 = 0;
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3421_: u8 = 0;
    let mut v___x_3422_: u8 = 0;
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: u8 = 0;
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: u8 = 0;
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: u8 = 0;
    let mut v___x_3441_: u8 = 0;
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3450_: u8 = 0;
    let mut v_a_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3458_: u8 = 0;
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut v_a_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_3332_ == 0 {
                    lean_inc(v_lhs_3333_);
                    v___x_3407_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_3333_, v___y_3339_);
                    v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
                    lean_inc(v_a_3408_);
                    lean_dec_ref(v___x_3407_);
                    lean_inc(v_rhs_3334_);
                    v___x_3409_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_3334_, v___y_3339_);
                    v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
                    lean_inc(v_a_3410_);
                    lean_dec_ref(v___x_3409_);
                    v___x_3411_ = l_Lean_Level_normalize(v_a_3408_);
                    lean_dec(v_a_3408_);
                    v___x_3412_ = l_Lean_Level_normalize(v_a_3410_);
                    lean_dec(v_a_3410_);
                    v___x_3413_ = lean_level_eq(v_lhs_3333_, v___x_3411_);
                    if v___x_3413_ == 0 {
                        lean_dec_ref(v___x_3336_);
                        lean_dec_ref(v___x_3335_);
                        lean_dec(v_rhs_3334_);
                        lean_dec(v_lhs_3333_);
                        lean_inc(v___y_3341_);
                        lean_inc_ref(v___y_3340_);
                        lean_inc(v___y_3339_);
                        lean_inc_ref(v___y_3338_);
                        v___x_3414_ = lean_is_level_def_eq(
                            v___x_3411_,
                            v___x_3412_,
                            v___y_3338_,
                            v___y_3339_,
                            v___y_3340_,
                            v___y_3341_,
                        );
                        return v___x_3414_;
                    } else {
                        v___x_3415_ = lean_level_eq(v_rhs_3334_, v___x_3412_);
                        if v___x_3415_ == 0 {
                            lean_dec_ref(v___x_3336_);
                            lean_dec_ref(v___x_3335_);
                            lean_dec(v_rhs_3334_);
                            lean_dec(v_lhs_3333_);
                            lean_inc(v___y_3341_);
                            lean_inc_ref(v___y_3340_);
                            lean_inc(v___y_3339_);
                            lean_inc_ref(v___y_3338_);
                            v___x_3416_ = lean_is_level_def_eq(
                                v___x_3411_,
                                v___x_3412_,
                                v___y_3338_,
                                v___y_3339_,
                                v___y_3340_,
                                v___y_3341_,
                            );
                            return v___x_3416_;
                        } else {
                            lean_dec(v___x_3412_);
                            lean_dec(v___x_3411_);
                            lean_inc(v___y_3341_);
                            lean_inc_ref(v___y_3340_);
                            lean_inc(v___y_3339_);
                            lean_inc_ref(v___y_3338_);
                            lean_inc(v_rhs_3334_);
                            lean_inc(v_lhs_3333_);
                            v___x_3417_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(
                                v_lhs_3333_,
                                v_rhs_3334_,
                                v___y_3338_,
                                v___y_3339_,
                                v___y_3340_,
                                v___y_3341_,
                            );
                            if lean_obj_tag(v___x_3417_) == 0 {
                                v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
                                v_isSharedCheck_3459_ = (!lean_is_exclusive(v___x_3417_)) as u8;
                                if v_isSharedCheck_3459_ == 0 {
                                    v___x_3420_ = v___x_3417_;
                                    v_isShared_3421_ = v_isSharedCheck_3459_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_3418_);
                                    lean_dec(v___x_3417_);
                                    v___x_3420_ = lean_box(0);
                                    v_isShared_3421_ = v_isSharedCheck_3459_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_3336_);
                                lean_dec_ref(v___x_3335_);
                                lean_dec(v_rhs_3334_);
                                lean_dec(v_lhs_3333_);
                                v_a_3460_ = lean_ctor_get(v___x_3417_, 0);
                                v_isSharedCheck_3467_ = (!lean_is_exclusive(v___x_3417_)) as u8;
                                if v_isSharedCheck_3467_ == 0 {
                                    v___x_3462_ = v___x_3417_;
                                    v_isShared_3463_ = v_isSharedCheck_3467_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_3460_);
                                    lean_dec(v___x_3417_);
                                    v___x_3462_ = lean_box(0);
                                    v_isShared_3463_ = v_isSharedCheck_3467_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3336_);
                    lean_dec_ref(v___x_3335_);
                    v___x_3468_ = l_Lean_Level_getOffset(v_lhs_3333_);
                    lean_dec(v_lhs_3333_);
                    v___x_3469_ = l_Lean_Level_getOffset(v_rhs_3334_);
                    lean_dec(v_rhs_3334_);
                    v___x_3470_ = lean_nat_dec_eq(v___x_3468_, v___x_3469_);
                    lean_dec(v___x_3469_);
                    lean_dec(v___x_3468_);
                    v___x_3471_ = lean_box((v___x_3470_) as usize);
                    v___x_3472_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3472_, 0, v___x_3471_);
                    return v___x_3472_;
                }
            }
            1 => {
                v_options_3344_ = lean_ctor_get(v___y_3340_, 2);
                v_hasTrace_3345_ = lean_ctor_get_uint8(
                    v_options_3344_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3345_ == 0 {
                    lean_dec_ref(v___x_3336_);
                    lean_dec_ref(v___x_3335_);
                    lean_dec(v_rhs_3334_);
                    lean_dec(v_lhs_3333_);
                    v___x_3346_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
                    return v___x_3346_;
                } else {
                    v_inheritedTraceOptions_3347_ = lean_ctor_get(v___y_3340_, 13);
                    v___x_3348_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0;
                    v___x_3349_ = l_Lean_Name_mkStr3(v___x_3335_, v___x_3336_, v___x_3348_);
                    v___x_3350_ =
                        l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9;
                    lean_inc(v___x_3349_);
                    v___x_3351_ = l_Lean_Name_append(v___x_3350_, v___x_3349_);
                    v___x_3352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3347_,
                        v_options_3344_,
                        v___x_3351_,
                    );
                    lean_dec(v___x_3351_);
                    if v___x_3352_ == 0 {
                        lean_dec(v___x_3349_);
                        lean_dec(v_rhs_3334_);
                        lean_dec(v_lhs_3333_);
                        v___x_3353_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
                        return v___x_3353_;
                    } else {
                        v___x_3354_ = l_Lean_MessageData_ofLevel(v_lhs_3333_);
                        v___x_3355_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
                        v___x_3356_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3356_, 0, v___x_3354_);
                        lean_ctor_set(v___x_3356_, 1, v___x_3355_);
                        v___x_3357_ = l_Lean_MessageData_ofLevel(v_rhs_3334_);
                        v___x_3358_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3358_, 0, v___x_3356_);
                        lean_ctor_set(v___x_3358_, 1, v___x_3357_);
                        v___x_3359_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_3349_, v___x_3358_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
                        if lean_obj_tag(v___x_3359_) == 0 {
                            lean_dec_ref_known(v___x_3359_, 1);
                            v___x_3360_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
                            return v___x_3360_;
                        } else {
                            v_a_3361_ = lean_ctor_get(v___x_3359_, 0);
                            v_isSharedCheck_3368_ = (!lean_is_exclusive(v___x_3359_)) as u8;
                            if v_isSharedCheck_3368_ == 0 {
                                v___x_3363_ = v___x_3359_;
                                v_isShared_3364_ = v_isSharedCheck_3368_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3361_);
                                lean_dec(v___x_3359_);
                                v___x_3363_ = lean_box(0);
                                v_isShared_3364_ = v_isSharedCheck_3368_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                if v_isShared_3364_ == 0 {
                    v___x_3366_ = v___x_3363_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
                    v___x_3366_ = v_reuseFailAlloc_3367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3366_;
            }
            4 => {
                if lean_obj_tag(v___y_3370_) == 0 {
                    v_a_3371_ = lean_ctor_get(v___y_3370_, 0);
                    v_isSharedCheck_3406_ = (!lean_is_exclusive(v___y_3370_)) as u8;
                    if v_isSharedCheck_3406_ == 0 {
                        v___x_3373_ = v___y_3370_;
                        v_isShared_3374_ = v_isSharedCheck_3406_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3371_);
                        lean_dec(v___y_3370_);
                        v___x_3373_ = lean_box(0);
                        v_isShared_3374_ = v_isSharedCheck_3406_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3336_);
                    lean_dec_ref(v___x_3335_);
                    lean_dec(v_rhs_3334_);
                    lean_dec(v_lhs_3333_);
                    return v___y_3370_;
                }
            }
            5 => {
                v___x_3375_ = (lean_unbox(v_a_3371_) as u8);
                lean_dec(v_a_3371_);
                if v___x_3375_ == 0 {
                    v___x_3376_ = l_Lean_Meta_Context_config(v___y_3338_);
                    v_isDefEqStuckEx_3377_ = lean_ctor_get_uint8(v___x_3376_, 4 as u32);
                    lean_dec_ref(v___x_3376_);
                    if v_isDefEqStuckEx_3377_ == 0 {
                        lean_dec_ref(v___x_3336_);
                        lean_dec_ref(v___x_3335_);
                        lean_dec(v_rhs_3334_);
                        lean_dec(v_lhs_3333_);
                        v___x_3378_ = lean_box((v_isDefEqStuckEx_3377_) as usize);
                        if v_isShared_3374_ == 0 {
                            lean_ctor_set(v___x_3373_, 0, v___x_3378_);
                            v___x_3380_ = v___x_3373_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
                            v___x_3380_ = v_reuseFailAlloc_3381_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_3382_ = l_Lean_Level_isMVar(v_lhs_3333_);
                        if v___x_3382_ == 0 {
                            v___x_3383_ = l_Lean_Level_isMVar(v_rhs_3334_);
                            if v___x_3383_ == 0 {
                                lean_dec_ref(v___x_3336_);
                                lean_dec_ref(v___x_3335_);
                                lean_dec(v_rhs_3334_);
                                lean_dec(v_lhs_3333_);
                                v___x_3384_ = lean_box((v___x_3383_) as usize);
                                if v_isShared_3374_ == 0 {
                                    lean_ctor_set(v___x_3373_, 0, v___x_3384_);
                                    v___x_3386_ = v___x_3373_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
                                    v___x_3386_ = v_reuseFailAlloc_3387_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_3373_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3373_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3373_);
                    lean_dec_ref(v___x_3336_);
                    lean_dec_ref(v___x_3335_);
                    v___x_3388_ =
                        l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(
                            v_lhs_3333_,
                            v_rhs_3334_,
                            v___y_3338_,
                            v___y_3339_,
                            v___y_3340_,
                            v___y_3341_,
                        );
                    if lean_obj_tag(v___x_3388_) == 0 {
                        v_isSharedCheck_3396_ = (!lean_is_exclusive(v___x_3388_)) as u8;
                        if v_isSharedCheck_3396_ == 0 {
                            v_unused_3397_ = lean_ctor_get(v___x_3388_, 0);
                            lean_dec(v_unused_3397_);
                            v___x_3390_ = v___x_3388_;
                            v_isShared_3391_ = v_isSharedCheck_3396_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec(v___x_3388_);
                            v___x_3390_ = lean_box(0);
                            v_isShared_3391_ = v_isSharedCheck_3396_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_3398_ = lean_ctor_get(v___x_3388_, 0);
                        v_isSharedCheck_3405_ = (!lean_is_exclusive(v___x_3388_)) as u8;
                        if v_isSharedCheck_3405_ == 0 {
                            v___x_3400_ = v___x_3388_;
                            v_isShared_3401_ = v_isSharedCheck_3405_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3398_);
                            lean_dec(v___x_3388_);
                            v___x_3400_ = lean_box(0);
                            v_isShared_3401_ = v_isSharedCheck_3405_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_3380_;
            }
            7 => {
                return v___x_3386_;
            }
            8 => {
                v___x_3392_ = lean_box((v___x_3337_) as usize);
                if v_isShared_3391_ == 0 {
                    lean_ctor_set(v___x_3390_, 0, v___x_3392_);
                    v___x_3394_ = v___x_3390_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
                    v___x_3394_ = v_reuseFailAlloc_3395_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3394_;
            }
            10 => {
                if v_isShared_3401_ == 0 {
                    v___x_3403_ = v___x_3400_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
                    v___x_3403_ = v_reuseFailAlloc_3404_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3403_;
            }
            12 => {
                v___x_3422_ = 2;
                v___x_3423_ = (lean_unbox(v_a_3418_) as u8);
                v___x_3424_ = l_Lean_instBEqLBool_beq(v___x_3423_, v___x_3422_);
                if v___x_3424_ == 0 {
                    lean_dec_ref(v___x_3336_);
                    lean_dec_ref(v___x_3335_);
                    lean_dec(v_rhs_3334_);
                    lean_dec(v_lhs_3333_);
                    v___x_3425_ = 1;
                    v___x_3426_ = (lean_unbox(v_a_3418_) as u8);
                    lean_dec(v_a_3418_);
                    v___x_3427_ = l_Lean_instBEqLBool_beq(v___x_3426_, v___x_3425_);
                    v___x_3428_ = lean_box((v___x_3427_) as usize);
                    if v_isShared_3421_ == 0 {
                        lean_ctor_set(v___x_3420_, 0, v___x_3428_);
                        v___x_3430_ = v___x_3420_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
                        v___x_3430_ = v_reuseFailAlloc_3431_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3420_);
                    lean_dec(v_a_3418_);
                    lean_inc(v___y_3341_);
                    lean_inc_ref(v___y_3340_);
                    lean_inc(v___y_3339_);
                    lean_inc_ref(v___y_3338_);
                    lean_inc(v_lhs_3333_);
                    lean_inc(v_rhs_3334_);
                    v___x_3432_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(
                        v_rhs_3334_,
                        v_lhs_3333_,
                        v___y_3338_,
                        v___y_3339_,
                        v___y_3340_,
                        v___y_3341_,
                    );
                    if lean_obj_tag(v___x_3432_) == 0 {
                        v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3450_ = (!lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3450_ == 0 {
                            v___x_3435_ = v___x_3432_;
                            v_isShared_3436_ = v_isSharedCheck_3450_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3433_);
                            lean_dec(v___x_3432_);
                            v___x_3435_ = lean_box(0);
                            v_isShared_3436_ = v_isSharedCheck_3450_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3336_);
                        lean_dec_ref(v___x_3335_);
                        lean_dec(v_rhs_3334_);
                        lean_dec(v_lhs_3333_);
                        v_a_3451_ = lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3458_ = (!lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3458_ == 0 {
                            v___x_3453_ = v___x_3432_;
                            v_isShared_3454_ = v_isSharedCheck_3458_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_3451_);
                            lean_dec(v___x_3432_);
                            v___x_3453_ = lean_box(0);
                            v_isShared_3454_ = v_isSharedCheck_3458_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            13 => {
                return v___x_3430_;
            }
            14 => {
                v___x_3437_ = (lean_unbox(v_a_3433_) as u8);
                v___x_3438_ = l_Lean_instBEqLBool_beq(v___x_3437_, v___x_3422_);
                if v___x_3438_ == 0 {
                    lean_dec_ref(v___x_3336_);
                    lean_dec_ref(v___x_3335_);
                    lean_dec(v_rhs_3334_);
                    lean_dec(v_lhs_3333_);
                    v___x_3439_ = 1;
                    v___x_3440_ = (lean_unbox(v_a_3433_) as u8);
                    lean_dec(v_a_3433_);
                    v___x_3441_ = l_Lean_instBEqLBool_beq(v___x_3440_, v___x_3439_);
                    v___x_3442_ = lean_box((v___x_3441_) as usize);
                    if v_isShared_3436_ == 0 {
                        lean_ctor_set(v___x_3435_, 0, v___x_3442_);
                        v___x_3444_ = v___x_3435_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
                        v___x_3444_ = v_reuseFailAlloc_3445_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3435_);
                    lean_dec(v_a_3433_);
                    lean_inc(v_lhs_3333_);
                    v___x_3446_ = l_Lean_Meta_hasAssignableLevelMVar(
                        v_lhs_3333_,
                        v___y_3338_,
                        v___y_3339_,
                        v___y_3340_,
                        v___y_3341_,
                    );
                    if lean_obj_tag(v___x_3446_) == 0 {
                        v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
                        lean_inc(v_a_3447_);
                        v___x_3448_ = (lean_unbox(v_a_3447_) as u8);
                        lean_dec(v_a_3447_);
                        if v___x_3448_ == 0 {
                            lean_dec_ref_known(v___x_3446_, 1);
                            lean_inc(v_rhs_3334_);
                            v___x_3449_ = l_Lean_Meta_hasAssignableLevelMVar(
                                v_rhs_3334_,
                                v___y_3338_,
                                v___y_3339_,
                                v___y_3340_,
                                v___y_3341_,
                            );
                            v___y_3370_ = v___x_3449_;
                            state = 4;
                            continue;
                        } else {
                            v___y_3370_ = v___x_3446_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_3370_ = v___x_3446_;
                        state = 4;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_3444_;
            }
            16 => {
                if v_isShared_3454_ == 0 {
                    v___x_3456_ = v___x_3453_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
                    v___x_3456_ = v_reuseFailAlloc_3457_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3456_;
            }
            18 => {
                if v_isShared_3463_ == 0 {
                    v___x_3465_ = v___x_3462_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
                    v___x_3465_ = v_reuseFailAlloc_3466_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(
    mut v___x_3473_: *mut LeanObject,
    mut v_lhs_3474_: *mut LeanObject,
    mut v_rhs_3475_: *mut LeanObject,
    mut v___x_3476_: *mut LeanObject,
    mut v___x_3477_: *mut LeanObject,
    mut v___x_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_15019__boxed_3484_: u8 = 0;
    let mut v___x_15022__boxed_3485_: u8 = 0;
    let mut v_res_3486_: *mut LeanObject = core::ptr::null_mut();
    v___x_15019__boxed_3484_ = (lean_unbox(v___x_3473_) as u8);
    v___x_15022__boxed_3485_ = (lean_unbox(v___x_3478_) as u8);
    v_res_3486_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(
        v___x_15019__boxed_3484_,
        v_lhs_3474_,
        v_rhs_3475_,
        v___x_3476_,
        v___x_3477_,
        v___x_15022__boxed_3485_,
        v___y_3479_,
        v___y_3480_,
        v___y_3481_,
        v___y_3482_,
    );
    lean_dec(v___y_3482_);
    lean_dec_ref(v___y_3481_);
    lean_dec(v___y_3480_);
    lean_dec_ref(v___y_3479_);
    return v_res_3486_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(
    mut v_x_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut v_a_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3487_) == 0 {
                    v_a_3489_ = lean_ctor_get(v_x_3487_, 0);
                    v_isSharedCheck_3496_ = (!lean_is_exclusive(v_x_3487_)) as u8;
                    if v_isSharedCheck_3496_ == 0 {
                        v___x_3491_ = v_x_3487_;
                        v_isShared_3492_ = v_isSharedCheck_3496_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3489_);
                        lean_dec(v_x_3487_);
                        v___x_3491_ = lean_box(0);
                        v_isShared_3492_ = v_isSharedCheck_3496_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3497_ = lean_ctor_get(v_x_3487_, 0);
                    v_isSharedCheck_3504_ = (!lean_is_exclusive(v_x_3487_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3499_ = v_x_3487_;
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3497_);
                        lean_dec(v_x_3487_);
                        v___x_3499_ = lean_box(0);
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3492_ == 0 {
                    lean_ctor_set_tag(v___x_3491_, 1);
                    v___x_3494_ = v___x_3491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
                    v___x_3494_ = v_reuseFailAlloc_3495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3494_;
            }
            3 => {
                if v_isShared_3500_ == 0 {
                    lean_ctor_set_tag(v___x_3499_, 0);
                    v___x_3502_ = v___x_3499_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
                    v___x_3502_ = v_reuseFailAlloc_3503_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg___boxed(
    mut v_x_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3507_: *mut LeanObject = core::ptr::null_mut();
    v_res_3507_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_x_3505_);
    return v_res_3507_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(
    mut v_sz_3508_: usize,
    mut v_i_3509_: usize,
    mut v_bs_3510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3511_: u8 = 0;
    let mut v_v_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: usize = 0;
    let mut v___x_3517_: usize = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3511_ = lean_usize_dec_lt(v_i_3509_, v_sz_3508_);
                if v___x_3511_ == 0 {
                    return v_bs_3510_;
                } else {
                    v_v_3512_ = lean_array_uget_borrowed(v_bs_3510_, v_i_3509_);
                    v_msg_3513_ = lean_ctor_get(v_v_3512_, 1);
                    lean_inc_ref(v_msg_3513_);
                    v___x_3514_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3515_ = lean_array_uset(v_bs_3510_, v_i_3509_, v___x_3514_);
                    v___x_3516_ = 1usize;
                    v___x_3517_ = lean_usize_add(v_i_3509_, v___x_3516_);
                    v___x_3518_ = lean_array_uset(v_bs_x27_3515_, v_i_3509_, v_msg_3513_);
                    v_i_3509_ = v___x_3517_;
                    v_bs_3510_ = v___x_3518_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7___boxed(
    mut v_sz_3520_: *mut LeanObject,
    mut v_i_3521_: *mut LeanObject,
    mut v_bs_3522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3523_: usize = 0;
    let mut v_i_boxed_3524_: usize = 0;
    let mut v_res_3525_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3523_ = lean_unbox_usize(v_sz_3520_);
    lean_dec(v_sz_3520_);
    v_i_boxed_3524_ = lean_unbox_usize(v_i_3521_);
    lean_dec(v_i_3521_);
    v_res_3525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(v_sz_boxed_3523_, v_i_boxed_3524_, v_bs_3522_);
    return v_res_3525_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(
    mut v_oldTraces_3526_: *mut LeanObject,
    mut v_data_3527_: *mut LeanObject,
    mut v_ref_3528_: *mut LeanObject,
    mut v_msg_3529_: *mut LeanObject,
    mut v___y_3530_: *mut LeanObject,
    mut v___y_3531_: *mut LeanObject,
    mut v___y_3532_: *mut LeanObject,
    mut v___y_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3547_: u8 = 0;
    let mut v_cancelTk_x3f_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3549_: u8 = 0;
    let mut v_inheritedTraceOptions_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3557_: usize = 0;
    let mut v___x_3558_: usize = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v_tid_3579_: u64 = 0;
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut v_unused_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_isSharedCheck_3599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3535_ = lean_ctor_get(v___y_3532_, 0);
                v_fileMap_3536_ = lean_ctor_get(v___y_3532_, 1);
                v_options_3537_ = lean_ctor_get(v___y_3532_, 2);
                v_currRecDepth_3538_ = lean_ctor_get(v___y_3532_, 3);
                v_maxRecDepth_3539_ = lean_ctor_get(v___y_3532_, 4);
                v_ref_3540_ = lean_ctor_get(v___y_3532_, 5);
                v_currNamespace_3541_ = lean_ctor_get(v___y_3532_, 6);
                v_openDecls_3542_ = lean_ctor_get(v___y_3532_, 7);
                v_initHeartbeats_3543_ = lean_ctor_get(v___y_3532_, 8);
                v_maxHeartbeats_3544_ = lean_ctor_get(v___y_3532_, 9);
                v_quotContext_3545_ = lean_ctor_get(v___y_3532_, 10);
                v_currMacroScope_3546_ = lean_ctor_get(v___y_3532_, 11);
                v_diag_3547_ = lean_ctor_get_uint8(
                    v___y_3532_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3548_ = lean_ctor_get(v___y_3532_, 12);
                v_suppressElabErrors_3549_ = lean_ctor_get_uint8(
                    v___y_3532_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3550_ = lean_ctor_get(v___y_3532_, 13);
                v___x_3551_ = lean_st_ref_get(v___y_3533_);
                v_traceState_3552_ = lean_ctor_get(v___x_3551_, 4);
                lean_inc_ref(v_traceState_3552_);
                lean_dec(v___x_3551_);
                v_traces_3553_ = lean_ctor_get(v_traceState_3552_, 0);
                lean_inc_ref(v_traces_3553_);
                lean_dec_ref(v_traceState_3552_);
                v_ref_3554_ = l_Lean_replaceRef(v_ref_3528_, v_ref_3540_);
                lean_inc_ref(v_inheritedTraceOptions_3550_);
                lean_inc(v_cancelTk_x3f_3548_);
                lean_inc(v_currMacroScope_3546_);
                lean_inc(v_quotContext_3545_);
                lean_inc(v_maxHeartbeats_3544_);
                lean_inc(v_initHeartbeats_3543_);
                lean_inc(v_openDecls_3542_);
                lean_inc(v_currNamespace_3541_);
                lean_inc(v_maxRecDepth_3539_);
                lean_inc(v_currRecDepth_3538_);
                lean_inc_ref(v_options_3537_);
                lean_inc_ref(v_fileMap_3536_);
                lean_inc_ref(v_fileName_3535_);
                v___x_3555_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3555_, 0, v_fileName_3535_);
                lean_ctor_set(v___x_3555_, 1, v_fileMap_3536_);
                lean_ctor_set(v___x_3555_, 2, v_options_3537_);
                lean_ctor_set(v___x_3555_, 3, v_currRecDepth_3538_);
                lean_ctor_set(v___x_3555_, 4, v_maxRecDepth_3539_);
                lean_ctor_set(v___x_3555_, 5, v_ref_3554_);
                lean_ctor_set(v___x_3555_, 6, v_currNamespace_3541_);
                lean_ctor_set(v___x_3555_, 7, v_openDecls_3542_);
                lean_ctor_set(v___x_3555_, 8, v_initHeartbeats_3543_);
                lean_ctor_set(v___x_3555_, 9, v_maxHeartbeats_3544_);
                lean_ctor_set(v___x_3555_, 10, v_quotContext_3545_);
                lean_ctor_set(v___x_3555_, 11, v_currMacroScope_3546_);
                lean_ctor_set(v___x_3555_, 12, v_cancelTk_x3f_3548_);
                lean_ctor_set(v___x_3555_, 13, v_inheritedTraceOptions_3550_);
                lean_ctor_set_uint8(
                    v___x_3555_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_3547_,
                );
                lean_ctor_set_uint8(
                    v___x_3555_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3549_,
                );
                v___x_3556_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3553_);
                lean_dec_ref(v_traces_3553_);
                v_sz_3557_ = lean_array_size(v___x_3556_);
                v___x_3558_ = 0usize;
                v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(v_sz_3557_, v___x_3558_, v___x_3556_);
                v_msg_3560_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v_msg_3560_, 0, v_data_3527_);
                lean_ctor_set(v_msg_3560_, 1, v_msg_3529_);
                lean_ctor_set(v_msg_3560_, 2, v___x_3559_);
                v___x_3561_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_3560_, v___y_3530_, v___y_3531_, v___x_3555_, v___y_3533_);
                lean_dec_ref_known(v___x_3555_, 14);
                v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
                v_isSharedCheck_3599_ = (!lean_is_exclusive(v___x_3561_)) as u8;
                if v_isSharedCheck_3599_ == 0 {
                    v___x_3564_ = v___x_3561_;
                    v_isShared_3565_ = v_isSharedCheck_3599_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3562_);
                    lean_dec(v___x_3561_);
                    v___x_3564_ = lean_box(0);
                    v_isShared_3565_ = v_isSharedCheck_3599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3566_ = lean_st_ref_take(v___y_3533_);
                v_traceState_3567_ = lean_ctor_get(v___x_3566_, 4);
                v_env_3568_ = lean_ctor_get(v___x_3566_, 0);
                v_nextMacroScope_3569_ = lean_ctor_get(v___x_3566_, 1);
                v_ngen_3570_ = lean_ctor_get(v___x_3566_, 2);
                v_auxDeclNGen_3571_ = lean_ctor_get(v___x_3566_, 3);
                v_cache_3572_ = lean_ctor_get(v___x_3566_, 5);
                v_messages_3573_ = lean_ctor_get(v___x_3566_, 6);
                v_infoState_3574_ = lean_ctor_get(v___x_3566_, 7);
                v_snapshotTasks_3575_ = lean_ctor_get(v___x_3566_, 8);
                v_isSharedCheck_3598_ = (!lean_is_exclusive(v___x_3566_)) as u8;
                if v_isSharedCheck_3598_ == 0 {
                    v___x_3577_ = v___x_3566_;
                    v_isShared_3578_ = v_isSharedCheck_3598_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3575_);
                    lean_inc(v_infoState_3574_);
                    lean_inc(v_messages_3573_);
                    lean_inc(v_cache_3572_);
                    lean_inc(v_traceState_3567_);
                    lean_inc(v_auxDeclNGen_3571_);
                    lean_inc(v_ngen_3570_);
                    lean_inc(v_nextMacroScope_3569_);
                    lean_inc(v_env_3568_);
                    lean_dec(v___x_3566_);
                    v___x_3577_ = lean_box(0);
                    v_isShared_3578_ = v_isSharedCheck_3598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3579_ = lean_ctor_get_uint64(
                    v_traceState_3567_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3596_ = (!lean_is_exclusive(v_traceState_3567_)) as u8;
                if v_isSharedCheck_3596_ == 0 {
                    v_unused_3597_ = lean_ctor_get(v_traceState_3567_, 0);
                    lean_dec(v_unused_3597_);
                    v___x_3581_ = v_traceState_3567_;
                    v_isShared_3582_ = v_isSharedCheck_3596_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_traceState_3567_);
                    v___x_3581_ = lean_box(0);
                    v_isShared_3582_ = v_isSharedCheck_3596_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3583_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3583_, 0, v_ref_3528_);
                lean_ctor_set(v___x_3583_, 1, v_a_3562_);
                v___x_3584_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3526_, v___x_3583_);
                if v_isShared_3582_ == 0 {
                    lean_ctor_set(v___x_3581_, 0, v___x_3584_);
                    v___x_3586_ = v___x_3581_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3584_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3595_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3579_,
                    );
                    v___x_3586_ = v_reuseFailAlloc_3595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3578_ == 0 {
                    lean_ctor_set(v___x_3577_, 4, v___x_3586_);
                    v___x_3588_ = v___x_3577_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_env_3568_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_nextMacroScope_3569_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_ngen_3570_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 3, v_auxDeclNGen_3571_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 4, v___x_3586_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 5, v_cache_3572_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 6, v_messages_3573_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 7, v_infoState_3574_);
                    lean_ctor_set(v_reuseFailAlloc_3594_, 8, v_snapshotTasks_3575_);
                    v___x_3588_ = v_reuseFailAlloc_3594_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3589_ = lean_st_ref_set(v___y_3533_, v___x_3588_);
                v___x_3590_ = lean_box(0);
                if v_isShared_3565_ == 0 {
                    lean_ctor_set(v___x_3564_, 0, v___x_3590_);
                    v___x_3592_ = v___x_3564_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
                    v___x_3592_ = v_reuseFailAlloc_3593_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(
    mut v_oldTraces_3600_: *mut LeanObject,
    mut v_data_3601_: *mut LeanObject,
    mut v_ref_3602_: *mut LeanObject,
    mut v_msg_3603_: *mut LeanObject,
    mut v___y_3604_: *mut LeanObject,
    mut v___y_3605_: *mut LeanObject,
    mut v___y_3606_: *mut LeanObject,
    mut v___y_3607_: *mut LeanObject,
    mut v___y_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3609_: *mut LeanObject = core::ptr::null_mut();
    v_res_3609_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_oldTraces_3600_, v_data_3601_, v_ref_3602_, v_msg_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
    lean_dec(v___y_3607_);
    lean_dec_ref(v___y_3606_);
    lean_dec(v___y_3605_);
    lean_dec_ref(v___y_3604_);
    return v_res_3609_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(
    mut v_e_3610_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_e_3610_) == 0 {
        let mut v___x_3611_: u8 = 0;
        v___x_3611_ = 2;
        return v___x_3611_;
    } else {
        let mut v_a_3612_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3613_: u8 = 0;
        v_a_3612_ = lean_ctor_get(v_e_3610_, 0);
        v___x_3613_ = (lean_unbox(v_a_3612_) as u8);
        if v___x_3613_ == 0 {
            let mut v___x_3614_: u8 = 0;
            v___x_3614_ = 1;
            return v___x_3614_;
        } else {
            let mut v___x_3615_: u8 = 0;
            v___x_3615_ = 0;
            return v___x_3615_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(
    mut v_e_3616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3617_: u8 = 0;
    let mut v_r_3618_: *mut LeanObject = core::ptr::null_mut();
    v_res_3617_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_e_3616_);
    lean_dec_ref(v_e_3616_);
    v_r_3618_ = lean_box((v_res_3617_) as usize);
    return v_r_3618_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    v___x_3620_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0;
    v___x_3621_ = l_Lean_stringToMessageData(v___x_3620_);
    return v___x_3621_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2()
-> f64 {
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: f64 = 0.0;
    v___x_3622_ = lean_unsigned_to_nat(1000);
    v___x_3623_ = lean_float_of_nat(v___x_3622_);
    return v___x_3623_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(
    mut v_cls_3624_: *mut LeanObject,
    mut v_collapsed_3625_: u8,
    mut v_tag_3626_: *mut LeanObject,
    mut v_opts_3627_: *mut LeanObject,
    mut v_clsEnabled_3628_: u8,
    mut v_oldTraces_3629_: *mut LeanObject,
    mut v_ref_3630_: *mut LeanObject,
    mut v_msg_3631_: *mut LeanObject,
    mut v_resStartStop_3632_: *mut LeanObject,
    mut v___y_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___y_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut v_fst_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3660_: u8 = 0;
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v_result_3664_: u8 = 0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: f64 = 0.0;
    let mut v_data_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: f64 = 0.0;
    let mut v___x_3678_: f64 = 0.0;
    let mut v_reuseFailAlloc_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3682_: u8 = 0;
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v_tid_3696_: u64 = 0;
    let mut v_traces_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3700_: u8 = 0;
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut v___y_3713_: f64 = 0.0;
    let mut v___x_3714_: f64 = 0.0;
    let mut v___x_3715_: f64 = 0.0;
    let mut v___x_3716_: f64 = 0.0;
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: u8 = 0;
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: f64 = 0.0;
    let mut v___x_3723_: f64 = 0.0;
    let mut v___x_3724_: f64 = 0.0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: f64 = 0.0;
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3638_ = lean_ctor_get(v_resStartStop_3632_, 0);
                v_snd_3639_ = lean_ctor_get(v_resStartStop_3632_, 1);
                v_isSharedCheck_3729_ = (!lean_is_exclusive(v_resStartStop_3632_)) as u8;
                if v_isSharedCheck_3729_ == 0 {
                    v___x_3641_ = v_resStartStop_3632_;
                    v_isShared_3642_ = v_isSharedCheck_3729_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3639_);
                    lean_inc(v_fst_3638_);
                    lean_dec(v_resStartStop_3632_);
                    v___x_3641_ = lean_box(0);
                    v_isShared_3642_ = v_isSharedCheck_3729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3656_ = lean_ctor_get(v_snd_3639_, 0);
                v_snd_3657_ = lean_ctor_get(v_snd_3639_, 1);
                v_isSharedCheck_3728_ = (!lean_is_exclusive(v_snd_3639_)) as u8;
                if v_isSharedCheck_3728_ == 0 {
                    v___x_3659_ = v_snd_3639_;
                    v_isShared_3660_ = v_isSharedCheck_3728_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_3657_);
                    lean_inc(v_fst_3656_);
                    lean_dec(v_snd_3639_);
                    v___x_3659_ = lean_box(0);
                    v_isShared_3660_ = v_isSharedCheck_3728_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                v___x_3646_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_oldTraces_3629_, v_data_3645_, v_ref_3630_, v___y_3644_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
                if lean_obj_tag(v___x_3646_) == 0 {
                    lean_dec_ref_known(v___x_3646_, 1);
                    v___x_3647_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_fst_3638_);
                    return v___x_3647_;
                } else {
                    lean_dec(v_fst_3638_);
                    v_a_3648_ = lean_ctor_get(v___x_3646_, 0);
                    v_isSharedCheck_3655_ = (!lean_is_exclusive(v___x_3646_)) as u8;
                    if v_isSharedCheck_3655_ == 0 {
                        v___x_3650_ = v___x_3646_;
                        v_isShared_3651_ = v_isSharedCheck_3655_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3648_);
                        lean_dec(v___x_3646_);
                        v___x_3650_ = lean_box(0);
                        v_isShared_3651_ = v_isSharedCheck_3655_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3651_ == 0 {
                    v___x_3653_ = v___x_3650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
                    v___x_3653_ = v_reuseFailAlloc_3654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3653_;
            }
            5 => {
                v___x_3661_ = l_Lean_trace_profiler;
                v___x_3662_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(
                    v_opts_3627_,
                    v___x_3661_,
                );
                if v___x_3662_ == 0 {
                    v___y_3682_ = v___x_3662_;
                    state = 9;
                    continue;
                } else {
                    v___x_3718_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_3719_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(
                        v_opts_3627_,
                        v___x_3718_,
                    );
                    if v___x_3719_ == 0 {
                        v___x_3720_ = l_Lean_trace_profiler_threshold;
                        v___x_3721_ =
                            l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(
                                v_opts_3627_,
                                v___x_3720_,
                            );
                        v___x_3722_ = lean_float_of_nat(v___x_3721_);
                        v___x_3723_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2);
                        v___x_3724_ = lean_float_div(v___x_3722_, v___x_3723_);
                        v___y_3713_ = v___x_3724_;
                        state = 14;
                        continue;
                    } else {
                        v___x_3725_ = l_Lean_trace_profiler_threshold;
                        v___x_3726_ =
                            l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(
                                v_opts_3627_,
                                v___x_3725_,
                            );
                        v___x_3727_ = lean_float_of_nat(v___x_3726_);
                        v___y_3713_ = v___x_3727_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                v_result_3664_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_fst_3638_);
                v___x_3665_ = l_Lean_TraceResult_toEmoji(v_result_3664_);
                v___x_3666_ = l_Lean_stringToMessageData(v___x_3665_);
                v___x_3667_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1);
                if v_isShared_3660_ == 0 {
                    lean_ctor_set_tag(v___x_3659_, 7);
                    lean_ctor_set(v___x_3659_, 1, v___x_3667_);
                    lean_ctor_set(v___x_3659_, 0, v___x_3666_);
                    v___x_3669_ = v___x_3659_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3666_);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 1, v___x_3667_);
                    v___x_3669_ = v_reuseFailAlloc_3680_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3642_ == 0 {
                    lean_ctor_set_tag(v___x_3641_, 7);
                    lean_ctor_set(v___x_3641_, 1, v_msg_3631_);
                    lean_ctor_set(v___x_3641_, 0, v___x_3669_);
                    v_msg_3671_ = v___x_3641_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3669_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_msg_3631_);
                    v_msg_3671_ = v_reuseFailAlloc_3679_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3672_ = lean_box((v_result_3664_) as usize);
                v___x_3673_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3673_, 0, v___x_3672_);
                v___x_3674_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
                lean_inc_ref(v_tag_3626_);
                lean_inc_ref(v___x_3673_);
                lean_inc(v_cls_3624_);
                v_data_3675_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_3675_, 0, v_cls_3624_);
                lean_ctor_set(v_data_3675_, 1, v___x_3673_);
                lean_ctor_set(v_data_3675_, 2, v_tag_3626_);
                lean_ctor_set_float(
                    v_data_3675_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3674_,
                );
                lean_ctor_set_float(
                    v_data_3675_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3674_,
                );
                lean_ctor_set_uint8(
                    v_data_3675_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_3625_,
                );
                if v___x_3662_ == 0 {
                    lean_dec_ref_known(v___x_3673_, 1);
                    lean_dec(v_snd_3657_);
                    lean_dec(v_fst_3656_);
                    lean_dec_ref(v_tag_3626_);
                    lean_dec(v_cls_3624_);
                    v___y_3644_ = v_msg_3671_;
                    v_data_3645_ = v_data_3675_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_3675_, 3);
                    v_data_3676_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_3676_, 0, v_cls_3624_);
                    lean_ctor_set(v_data_3676_, 1, v___x_3673_);
                    lean_ctor_set(v_data_3676_, 2, v_tag_3626_);
                    v___x_3677_ = lean_unbox_float(v_fst_3656_);
                    lean_dec(v_fst_3656_);
                    lean_ctor_set_float(
                        v_data_3676_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_3677_,
                    );
                    v___x_3678_ = lean_unbox_float(v_snd_3657_);
                    lean_dec(v_snd_3657_);
                    lean_ctor_set_float(
                        v_data_3676_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_3678_,
                    );
                    lean_ctor_set_uint8(
                        v_data_3676_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_collapsed_3625_,
                    );
                    v___y_3644_ = v_msg_3671_;
                    v_data_3645_ = v_data_3676_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                if v_clsEnabled_3628_ == 0 {
                    if v___y_3682_ == 0 {
                        lean_del_object(v___x_3659_);
                        lean_dec(v_snd_3657_);
                        lean_dec(v_fst_3656_);
                        lean_del_object(v___x_3641_);
                        lean_dec_ref(v_msg_3631_);
                        lean_dec(v_ref_3630_);
                        lean_dec_ref(v_tag_3626_);
                        lean_dec(v_cls_3624_);
                        v___x_3683_ = lean_st_ref_take(v___y_3636_);
                        v_traceState_3684_ = lean_ctor_get(v___x_3683_, 4);
                        v_env_3685_ = lean_ctor_get(v___x_3683_, 0);
                        v_nextMacroScope_3686_ = lean_ctor_get(v___x_3683_, 1);
                        v_ngen_3687_ = lean_ctor_get(v___x_3683_, 2);
                        v_auxDeclNGen_3688_ = lean_ctor_get(v___x_3683_, 3);
                        v_cache_3689_ = lean_ctor_get(v___x_3683_, 5);
                        v_messages_3690_ = lean_ctor_get(v___x_3683_, 6);
                        v_infoState_3691_ = lean_ctor_get(v___x_3683_, 7);
                        v_snapshotTasks_3692_ = lean_ctor_get(v___x_3683_, 8);
                        v_isSharedCheck_3711_ = (!lean_is_exclusive(v___x_3683_)) as u8;
                        if v_isSharedCheck_3711_ == 0 {
                            v___x_3694_ = v___x_3683_;
                            v_isShared_3695_ = v_isSharedCheck_3711_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_3692_);
                            lean_inc(v_infoState_3691_);
                            lean_inc(v_messages_3690_);
                            lean_inc(v_cache_3689_);
                            lean_inc(v_traceState_3684_);
                            lean_inc(v_auxDeclNGen_3688_);
                            lean_inc(v_ngen_3687_);
                            lean_inc(v_nextMacroScope_3686_);
                            lean_inc(v_env_3685_);
                            lean_dec(v___x_3683_);
                            v___x_3694_ = lean_box(0);
                            v_isShared_3695_ = v_isSharedCheck_3711_;
                            state = 10;
                            continue;
                        }
                    } else {
                        state = 6;
                        continue;
                    }
                } else {
                    state = 6;
                    continue;
                }
            }
            10 => {
                v_tid_3696_ = lean_ctor_get_uint64(
                    v_traceState_3684_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3697_ = lean_ctor_get(v_traceState_3684_, 0);
                v_isSharedCheck_3710_ = (!lean_is_exclusive(v_traceState_3684_)) as u8;
                if v_isSharedCheck_3710_ == 0 {
                    v___x_3699_ = v_traceState_3684_;
                    v_isShared_3700_ = v_isSharedCheck_3710_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_traces_3697_);
                    lean_dec(v_traceState_3684_);
                    v___x_3699_ = lean_box(0);
                    v_isShared_3700_ = v_isSharedCheck_3710_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3701_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_3629_, v_traces_3697_);
                lean_dec_ref(v_traces_3697_);
                if v_isShared_3700_ == 0 {
                    lean_ctor_set(v___x_3699_, 0, v___x_3701_);
                    v___x_3703_ = v___x_3699_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3701_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3709_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3696_,
                    );
                    v___x_3703_ = v_reuseFailAlloc_3709_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3695_ == 0 {
                    lean_ctor_set(v___x_3694_, 4, v___x_3703_);
                    v___x_3705_ = v___x_3694_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_env_3685_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_nextMacroScope_3686_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_ngen_3687_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 3, v_auxDeclNGen_3688_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 4, v___x_3703_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 5, v_cache_3689_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 6, v_messages_3690_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 7, v_infoState_3691_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 8, v_snapshotTasks_3692_);
                    v___x_3705_ = v_reuseFailAlloc_3708_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_3706_ = lean_st_ref_set(v___y_3636_, v___x_3705_);
                v___x_3707_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_fst_3638_);
                return v___x_3707_;
            }
            14 => {
                v___x_3714_ = lean_unbox_float(v_snd_3657_);
                v___x_3715_ = lean_unbox_float(v_fst_3656_);
                v___x_3716_ = lean_float_sub(v___x_3714_, v___x_3715_);
                v___x_3717_ = lean_float_decLt(v___y_3713_, v___x_3716_);
                v___y_3682_ = v___x_3717_;
                state = 9;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(
    mut v_cls_3730_: *mut LeanObject,
    mut v_collapsed_3731_: *mut LeanObject,
    mut v_tag_3732_: *mut LeanObject,
    mut v_opts_3733_: *mut LeanObject,
    mut v_clsEnabled_3734_: *mut LeanObject,
    mut v_oldTraces_3735_: *mut LeanObject,
    mut v_ref_3736_: *mut LeanObject,
    mut v_msg_3737_: *mut LeanObject,
    mut v_resStartStop_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_3744_: u8 = 0;
    let mut v_clsEnabled_boxed_3745_: u8 = 0;
    let mut v_res_3746_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3744_ = (lean_unbox(v_collapsed_3731_) as u8);
    v_clsEnabled_boxed_3745_ = (lean_unbox(v_clsEnabled_3734_) as u8);
    v_res_3746_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_3730_, v_collapsed_boxed_3744_, v_tag_3732_, v_opts_3733_, v_clsEnabled_boxed_3745_, v_oldTraces_3735_, v_ref_3736_, v_msg_3737_, v_resStartStop_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
    lean_dec(v___y_3742_);
    lean_dec_ref(v___y_3741_);
    lean_dec(v___y_3740_);
    lean_dec_ref(v___y_3739_);
    lean_dec_ref(v_opts_3733_);
    return v_res_3746_;
}
pub unsafe fn _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0() -> f64 {
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: f64 = 0.0;
    v___x_3747_ = lean_unsigned_to_nat(1000000000);
    v___x_3748_ = lean_float_of_nat(v___x_3747_);
    return v___x_3748_;
}
pub unsafe fn _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1() -> *mut LeanObject {
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_3749_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3749_;
}
pub unsafe fn _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2() -> *mut LeanObject {
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    v___x_3750_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once),
        _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1,
    );
    v___x_3751_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3751_, 0, v___x_3750_);
    return v___x_3751_;
}
pub unsafe fn _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3() -> *mut LeanObject {
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    v___x_3752_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once),
        _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2,
    );
    v___x_3753_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3753_, 0, v___x_3752_);
    lean_ctor_set(v___x_3753_, 1, v___x_3752_);
    return v___x_3753_;
}
pub unsafe fn _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8() -> *mut LeanObject {
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_Meta_isLevelDefEqAuxImpl___closed__7;
    v___x_3763_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9;
    v___x_3764_ = l_Lean_Name_append(v___x_3763_, v___x_3762_);
    return v___x_3764_;
}
pub unsafe fn lean_is_level_def_eq(
    mut v_x_3765_: *mut LeanObject,
    mut v_x_3766_: *mut LeanObject,
    mut v_a_3767_: *mut LeanObject,
    mut v_a_3768_: *mut LeanObject,
    mut v_a_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: u8 = 0;
    let mut v___y_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: u8 = 0;
    let mut v___y_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: f64 = 0.0;
    let mut v___x_3789_: f64 = 0.0;
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3797_: u8 = 0;
    let mut v___y_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: u8 = 0;
    let mut v___y_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: f64 = 0.0;
    let mut v___x_3812_: f64 = 0.0;
    let mut v___x_3813_: f64 = 0.0;
    let mut v___x_3814_: f64 = 0.0;
    let mut v___x_3815_: f64 = 0.0;
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: u8 = 0;
    let mut v___y_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3827_: u8 = 0;
    let mut v___y_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3831_: u8 = 0;
    let mut v___y_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3849_: u8 = 0;
    let mut v_inheritedTraceOptions_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: u8 = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut v_a_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3874_: u8 = 0;
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3878_: u8 = 0;
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3888_: u8 = 0;
    let mut v_a_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v___y_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3900_: u8 = 0;
    let mut v___y_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3903_: u8 = 0;
    let mut v___y_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: u8 = 0;
    let mut v___y_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3927_: u8 = 0;
    let mut v_inheritedTraceOptions_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3932_: u8 = 0;
    let mut v___y_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3935_: u8 = 0;
    let mut v___y_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3940_: u8 = 0;
    let mut v___y_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: u8 = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3965_: u8 = 0;
    let mut v_unused_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3968_: u8 = 0;
    let mut v___y_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3973_: u8 = 0;
    let mut v___y_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3986_: u8 = 0;
    let mut v___y_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3988_: u8 = 0;
    let mut v___y_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v___x_4011_: u8 = 0;
    let mut v_lhs_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4031_: u8 = 0;
    let mut v_cancelTk_x3f_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4033_: u8 = 0;
    let mut v_inheritedTraceOptions_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4035_: u8 = 0;
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: u8 = 0;
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: u8 = 0;
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3765_) == 1 {
                    if lean_obj_tag(v_x_3766_) == 1 {
                        v_a_4053_ = lean_ctor_get(v_x_3765_, 0);
                        lean_inc(v_a_4053_);
                        lean_dec_ref_known(v_x_3765_, 1);
                        v_a_4054_ = lean_ctor_get(v_x_3766_, 0);
                        lean_inc(v_a_4054_);
                        lean_dec_ref_known(v_x_3766_, 1);
                        v___x_4055_ = lean_is_level_def_eq(
                            v_a_4053_, v_a_4054_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_,
                        );
                        return v___x_4055_;
                    } else {
                        v_lhs_4013_ = v_x_3765_;
                        v_rhs_4014_ = v_x_3766_;
                        v___y_4015_ = v_a_3767_;
                        v___y_4016_ = v_a_3768_;
                        v___y_4017_ = v_a_3769_;
                        v___y_4018_ = v_a_3770_;
                        state = 17;
                        continue;
                    }
                } else {
                    v_lhs_4013_ = v_x_3765_;
                    v_rhs_4014_ = v_x_3766_;
                    v___y_4015_ = v_a_3767_;
                    v___y_4016_ = v_a_3768_;
                    v___y_4017_ = v_a_3769_;
                    v___y_4018_ = v_a_3770_;
                    state = 17;
                    continue;
                }
            }
            1 => {
                v___x_3787_ = lean_io_get_num_heartbeats();
                v___x_3788_ = lean_float_of_nat(v___y_3785_);
                v___x_3789_ = lean_float_of_nat(v___x_3787_);
                v___x_3790_ = lean_box_float(v___x_3788_);
                v___x_3791_ = lean_box_float(v___x_3789_);
                v___x_3792_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3792_, 0, v___x_3790_);
                lean_ctor_set(v___x_3792_, 1, v___x_3791_);
                v___x_3793_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3793_, 0, v_a_3786_);
                lean_ctor_set(v___x_3793_, 1, v___x_3792_);
                lean_inc_ref(v___y_3773_);
                lean_inc(v___y_3775_);
                v___x_3794_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_3775_, v___y_3777_, v___y_3773_, v___y_3778_, v___y_3774_, v___y_3781_, v___y_3783_, v___y_3782_, v___x_3793_, v___y_3779_, v___y_3776_, v___y_3780_, v___y_3784_);
                lean_dec(v___y_3784_);
                lean_dec_ref(v___y_3780_);
                lean_dec(v___y_3776_);
                lean_dec_ref(v___y_3779_);
                lean_dec_ref(v___y_3778_);
                return v___x_3794_;
            }
            2 => {
                v___x_3810_ = lean_io_mono_nanos_now();
                v___x_3811_ = lean_float_of_nat(v___y_3808_);
                v___x_3812_ = lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once),
                    _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0,
                );
                v___x_3813_ = lean_float_div(v___x_3811_, v___x_3812_);
                v___x_3814_ = lean_float_of_nat(v___x_3810_);
                v___x_3815_ = lean_float_div(v___x_3814_, v___x_3812_);
                v___x_3816_ = lean_box_float(v___x_3813_);
                v___x_3817_ = lean_box_float(v___x_3815_);
                v___x_3818_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3818_, 0, v___x_3816_);
                lean_ctor_set(v___x_3818_, 1, v___x_3817_);
                v___x_3819_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3819_, 0, v_a_3809_);
                lean_ctor_set(v___x_3819_, 1, v___x_3818_);
                lean_inc_ref(v___y_3796_);
                lean_inc(v___y_3798_);
                v___x_3820_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_3798_, v___y_3800_, v___y_3796_, v___y_3801_, v___y_3797_, v___y_3804_, v___y_3806_, v___y_3805_, v___x_3819_, v___y_3802_, v___y_3799_, v___y_3803_, v___y_3807_);
                lean_dec(v___y_3807_);
                lean_dec_ref(v___y_3803_);
                lean_dec(v___y_3799_);
                lean_dec_ref(v___y_3802_);
                lean_dec_ref(v___y_3801_);
                return v___x_3820_;
            }
            3 => {
                v___x_3852_ = l_Lean_maxRecDepth;
                v___x_3853_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(
                    v___y_3829_,
                    v___x_3852_,
                );
                v___x_3854_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3854_, 0, v_fileName_3838_);
                lean_ctor_set(v___x_3854_, 1, v_fileMap_3839_);
                lean_ctor_set(v___x_3854_, 2, v___y_3829_);
                lean_ctor_set(v___x_3854_, 3, v_currRecDepth_3840_);
                lean_ctor_set(v___x_3854_, 4, v___x_3853_);
                lean_ctor_set(v___x_3854_, 5, v_ref_3841_);
                lean_ctor_set(v___x_3854_, 6, v_currNamespace_3842_);
                lean_ctor_set(v___x_3854_, 7, v_openDecls_3843_);
                lean_ctor_set(v___x_3854_, 8, v_initHeartbeats_3844_);
                lean_ctor_set(v___x_3854_, 9, v_maxHeartbeats_3845_);
                lean_ctor_set(v___x_3854_, 10, v_quotContext_3846_);
                lean_ctor_set(v___x_3854_, 11, v_currMacroScope_3847_);
                lean_ctor_set(v___x_3854_, 12, v_cancelTk_x3f_3848_);
                lean_ctor_set(v___x_3854_, 13, v_inheritedTraceOptions_3850_);
                lean_ctor_set_uint8(
                    v___x_3854_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_3831_,
                );
                lean_ctor_set_uint8(
                    v___x_3854_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3849_,
                );
                v___x_3855_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_3823_, v___y_3830_, v___y_3825_, v___x_3854_, v___y_3851_);
                lean_dec(v___y_3851_);
                lean_dec_ref_known(v___x_3854_, 14);
                v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
                lean_inc(v_a_3856_);
                lean_dec_ref(v___x_3855_);
                v___x_3857_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_3856_, v___y_3830_, v___y_3825_, v___y_3835_, v___y_3837_);
                lean_dec_ref(v___y_3835_);
                v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
                lean_inc(v_a_3858_);
                lean_dec_ref(v___x_3857_);
                v___x_3859_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3860_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(
                    v___y_3828_,
                    v___x_3859_,
                );
                if v___x_3860_ == 0 {
                    v___x_3861_ = lean_io_mono_nanos_now();
                    lean_inc(v___y_3837_);
                    lean_inc_ref(v___y_3832_);
                    lean_inc(v___y_3825_);
                    lean_inc_ref(v___y_3830_);
                    v___x_3862_ = lean_apply_5(
                        v___y_3834_,
                        v___y_3830_,
                        v___y_3825_,
                        v___y_3832_,
                        v___y_3837_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3862_) == 0 {
                        v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
                        v_isSharedCheck_3870_ = (!lean_is_exclusive(v___x_3862_)) as u8;
                        if v_isSharedCheck_3870_ == 0 {
                            v___x_3865_ = v___x_3862_;
                            v_isShared_3866_ = v_isSharedCheck_3870_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3863_);
                            lean_dec(v___x_3862_);
                            v___x_3865_ = lean_box(0);
                            v_isShared_3866_ = v_isSharedCheck_3870_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3871_ = lean_ctor_get(v___x_3862_, 0);
                        v_isSharedCheck_3878_ = (!lean_is_exclusive(v___x_3862_)) as u8;
                        if v_isSharedCheck_3878_ == 0 {
                            v___x_3873_ = v___x_3862_;
                            v_isShared_3874_ = v_isSharedCheck_3878_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3871_);
                            lean_dec(v___x_3862_);
                            v___x_3873_ = lean_box(0);
                            v_isShared_3874_ = v_isSharedCheck_3878_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_3879_ = lean_io_get_num_heartbeats();
                    lean_inc(v___y_3837_);
                    lean_inc_ref(v___y_3832_);
                    lean_inc(v___y_3825_);
                    lean_inc_ref(v___y_3830_);
                    v___x_3880_ = lean_apply_5(
                        v___y_3834_,
                        v___y_3830_,
                        v___y_3825_,
                        v___y_3832_,
                        v___y_3837_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3880_) == 0 {
                        v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
                        v_isSharedCheck_3888_ = (!lean_is_exclusive(v___x_3880_)) as u8;
                        if v_isSharedCheck_3888_ == 0 {
                            v___x_3883_ = v___x_3880_;
                            v_isShared_3884_ = v_isSharedCheck_3888_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3881_);
                            lean_dec(v___x_3880_);
                            v___x_3883_ = lean_box(0);
                            v_isShared_3884_ = v_isSharedCheck_3888_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_3889_ = lean_ctor_get(v___x_3880_, 0);
                        v_isSharedCheck_3896_ = (!lean_is_exclusive(v___x_3880_)) as u8;
                        if v_isSharedCheck_3896_ == 0 {
                            v___x_3891_ = v___x_3880_;
                            v_isShared_3892_ = v_isSharedCheck_3896_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3889_);
                            lean_dec(v___x_3880_);
                            v___x_3891_ = lean_box(0);
                            v_isShared_3892_ = v_isSharedCheck_3896_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3866_ == 0 {
                    lean_ctor_set_tag(v___x_3865_, 1);
                    v___x_3868_ = v___x_3865_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
                    v___x_3868_ = v_reuseFailAlloc_3869_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3796_ = v___y_3822_;
                v___y_3797_ = v___y_3824_;
                v___y_3798_ = v___y_3826_;
                v___y_3799_ = v___y_3825_;
                v___y_3800_ = v___y_3827_;
                v___y_3801_ = v___y_3828_;
                v___y_3802_ = v___y_3830_;
                v___y_3803_ = v___y_3832_;
                v___y_3804_ = v___y_3833_;
                v___y_3805_ = v_a_3858_;
                v___y_3806_ = v___y_3836_;
                v___y_3807_ = v___y_3837_;
                v___y_3808_ = v___x_3861_;
                v_a_3809_ = v___x_3868_;
                state = 2;
                continue;
            }
            6 => {
                if v_isShared_3874_ == 0 {
                    lean_ctor_set_tag(v___x_3873_, 0);
                    v___x_3876_ = v___x_3873_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
                    v___x_3876_ = v_reuseFailAlloc_3877_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3796_ = v___y_3822_;
                v___y_3797_ = v___y_3824_;
                v___y_3798_ = v___y_3826_;
                v___y_3799_ = v___y_3825_;
                v___y_3800_ = v___y_3827_;
                v___y_3801_ = v___y_3828_;
                v___y_3802_ = v___y_3830_;
                v___y_3803_ = v___y_3832_;
                v___y_3804_ = v___y_3833_;
                v___y_3805_ = v_a_3858_;
                v___y_3806_ = v___y_3836_;
                v___y_3807_ = v___y_3837_;
                v___y_3808_ = v___x_3861_;
                v_a_3809_ = v___x_3876_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3884_ == 0 {
                    lean_ctor_set_tag(v___x_3883_, 1);
                    v___x_3886_ = v___x_3883_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
                    v___x_3886_ = v_reuseFailAlloc_3887_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_3773_ = v___y_3822_;
                v___y_3774_ = v___y_3824_;
                v___y_3775_ = v___y_3826_;
                v___y_3776_ = v___y_3825_;
                v___y_3777_ = v___y_3827_;
                v___y_3778_ = v___y_3828_;
                v___y_3779_ = v___y_3830_;
                v___y_3780_ = v___y_3832_;
                v___y_3781_ = v___y_3833_;
                v___y_3782_ = v_a_3858_;
                v___y_3783_ = v___y_3836_;
                v___y_3784_ = v___y_3837_;
                v___y_3785_ = v___x_3879_;
                v_a_3786_ = v___x_3886_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_3892_ == 0 {
                    lean_ctor_set_tag(v___x_3891_, 0);
                    v___x_3894_ = v___x_3891_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_3773_ = v___y_3822_;
                v___y_3774_ = v___y_3824_;
                v___y_3775_ = v___y_3826_;
                v___y_3776_ = v___y_3825_;
                v___y_3777_ = v___y_3827_;
                v___y_3778_ = v___y_3828_;
                v___y_3779_ = v___y_3830_;
                v___y_3780_ = v___y_3832_;
                v___y_3781_ = v___y_3833_;
                v___y_3782_ = v_a_3858_;
                v___y_3783_ = v___y_3836_;
                v___y_3784_ = v___y_3837_;
                v___y_3785_ = v___x_3879_;
                v_a_3786_ = v___x_3894_;
                state = 1;
                continue;
            }
            12 => {
                v_fileName_3916_ = lean_ctor_get(v___y_3914_, 0);
                lean_inc_ref(v_fileName_3916_);
                v_fileMap_3917_ = lean_ctor_get(v___y_3914_, 1);
                lean_inc_ref(v_fileMap_3917_);
                v_currRecDepth_3918_ = lean_ctor_get(v___y_3914_, 3);
                lean_inc(v_currRecDepth_3918_);
                v_ref_3919_ = lean_ctor_get(v___y_3914_, 5);
                lean_inc(v_ref_3919_);
                v_currNamespace_3920_ = lean_ctor_get(v___y_3914_, 6);
                lean_inc(v_currNamespace_3920_);
                v_openDecls_3921_ = lean_ctor_get(v___y_3914_, 7);
                lean_inc(v_openDecls_3921_);
                v_initHeartbeats_3922_ = lean_ctor_get(v___y_3914_, 8);
                lean_inc(v_initHeartbeats_3922_);
                v_maxHeartbeats_3923_ = lean_ctor_get(v___y_3914_, 9);
                lean_inc(v_maxHeartbeats_3923_);
                v_quotContext_3924_ = lean_ctor_get(v___y_3914_, 10);
                lean_inc(v_quotContext_3924_);
                v_currMacroScope_3925_ = lean_ctor_get(v___y_3914_, 11);
                lean_inc(v_currMacroScope_3925_);
                v_cancelTk_x3f_3926_ = lean_ctor_get(v___y_3914_, 12);
                lean_inc(v_cancelTk_x3f_3926_);
                v_suppressElabErrors_3927_ = lean_ctor_get_uint8(
                    v___y_3914_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3928_ = lean_ctor_get(v___y_3914_, 13);
                lean_inc_ref(v_inheritedTraceOptions_3928_);
                lean_dec_ref(v___y_3914_);
                v___y_3822_ = v___y_3898_;
                v___y_3823_ = v___y_3899_;
                v___y_3824_ = v___y_3900_;
                v___y_3825_ = v___y_3901_;
                v___y_3826_ = v___y_3902_;
                v___y_3827_ = v___y_3903_;
                v___y_3828_ = v___y_3904_;
                v___y_3829_ = v___y_3905_;
                v___y_3830_ = v___y_3906_;
                v___y_3831_ = v___y_3907_;
                v___y_3832_ = v___y_3908_;
                v___y_3833_ = v___y_3909_;
                v___y_3834_ = v___y_3910_;
                v___y_3835_ = v___y_3911_;
                v___y_3836_ = v___y_3912_;
                v___y_3837_ = v___y_3913_;
                v_fileName_3838_ = v_fileName_3916_;
                v_fileMap_3839_ = v_fileMap_3917_;
                v_currRecDepth_3840_ = v_currRecDepth_3918_;
                v_ref_3841_ = v_ref_3919_;
                v_currNamespace_3842_ = v_currNamespace_3920_;
                v_openDecls_3843_ = v_openDecls_3921_;
                v_initHeartbeats_3844_ = v_initHeartbeats_3922_;
                v_maxHeartbeats_3845_ = v_maxHeartbeats_3923_;
                v_quotContext_3846_ = v_quotContext_3924_;
                v_currMacroScope_3847_ = v_currMacroScope_3925_;
                v_cancelTk_x3f_3848_ = v_cancelTk_x3f_3926_;
                v_suppressElabErrors_3849_ = v_suppressElabErrors_3927_;
                v_inheritedTraceOptions_3850_ = v_inheritedTraceOptions_3928_;
                v___y_3851_ = v___y_3915_;
                state = 3;
                continue;
            }
            13 => {
                if v___y_3946_ == 0 {
                    v___x_3947_ = lean_st_ref_take(v___y_3945_);
                    v_env_3948_ = lean_ctor_get(v___x_3947_, 0);
                    v_nextMacroScope_3949_ = lean_ctor_get(v___x_3947_, 1);
                    v_ngen_3950_ = lean_ctor_get(v___x_3947_, 2);
                    v_auxDeclNGen_3951_ = lean_ctor_get(v___x_3947_, 3);
                    v_traceState_3952_ = lean_ctor_get(v___x_3947_, 4);
                    v_messages_3953_ = lean_ctor_get(v___x_3947_, 6);
                    v_infoState_3954_ = lean_ctor_get(v___x_3947_, 7);
                    v_snapshotTasks_3955_ = lean_ctor_get(v___x_3947_, 8);
                    v_isSharedCheck_3965_ = (!lean_is_exclusive(v___x_3947_)) as u8;
                    if v_isSharedCheck_3965_ == 0 {
                        v_unused_3966_ = lean_ctor_get(v___x_3947_, 5);
                        lean_dec(v_unused_3966_);
                        v___x_3957_ = v___x_3947_;
                        v_isShared_3958_ = v_isSharedCheck_3965_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_3955_);
                        lean_inc(v_infoState_3954_);
                        lean_inc(v_messages_3953_);
                        lean_inc(v_traceState_3952_);
                        lean_inc(v_auxDeclNGen_3951_);
                        lean_inc(v_ngen_3950_);
                        lean_inc(v_nextMacroScope_3949_);
                        lean_inc(v_env_3948_);
                        lean_dec(v___x_3947_);
                        v___x_3957_ = lean_box(0);
                        v_isShared_3958_ = v_isSharedCheck_3965_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_inc(v___y_3945_);
                    lean_inc_ref(v___y_3943_);
                    v___y_3898_ = v___y_3930_;
                    v___y_3899_ = v___y_3931_;
                    v___y_3900_ = v___y_3932_;
                    v___y_3901_ = v___y_3933_;
                    v___y_3902_ = v___y_3934_;
                    v___y_3903_ = v___y_3935_;
                    v___y_3904_ = v___y_3936_;
                    v___y_3905_ = v___y_3937_;
                    v___y_3906_ = v___y_3938_;
                    v___y_3907_ = v___y_3940_;
                    v___y_3908_ = v___y_3939_;
                    v___y_3909_ = v___y_3941_;
                    v___y_3910_ = v___y_3942_;
                    v___y_3911_ = v___y_3943_;
                    v___y_3912_ = v___y_3944_;
                    v___y_3913_ = v___y_3945_;
                    v___y_3914_ = v___y_3943_;
                    v___y_3915_ = v___y_3945_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v___x_3959_ = l_Lean_Kernel_enableDiag(v_env_3948_, v___y_3940_);
                v___x_3960_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once),
                    _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3,
                );
                if v_isShared_3958_ == 0 {
                    lean_ctor_set(v___x_3957_, 5, v___x_3960_);
                    lean_ctor_set(v___x_3957_, 0, v___x_3959_);
                    v___x_3962_ = v___x_3957_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3959_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_nextMacroScope_3949_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_ngen_3950_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_auxDeclNGen_3951_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_traceState_3952_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 5, v___x_3960_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 6, v_messages_3953_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 7, v_infoState_3954_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 8, v_snapshotTasks_3955_);
                    v___x_3962_ = v_reuseFailAlloc_3964_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3963_ = lean_st_ref_set(v___y_3945_, v___x_3962_);
                lean_inc(v___y_3945_);
                lean_inc_ref(v___y_3943_);
                v___y_3898_ = v___y_3930_;
                v___y_3899_ = v___y_3931_;
                v___y_3900_ = v___y_3932_;
                v___y_3901_ = v___y_3933_;
                v___y_3902_ = v___y_3934_;
                v___y_3903_ = v___y_3935_;
                v___y_3904_ = v___y_3936_;
                v___y_3905_ = v___y_3937_;
                v___y_3906_ = v___y_3938_;
                v___y_3907_ = v___y_3940_;
                v___y_3908_ = v___y_3939_;
                v___y_3909_ = v___y_3941_;
                v___y_3910_ = v___y_3942_;
                v___y_3911_ = v___y_3943_;
                v___y_3912_ = v___y_3944_;
                v___y_3913_ = v___y_3945_;
                v___y_3914_ = v___y_3943_;
                v___y_3915_ = v___y_3945_;
                state = 12;
                continue;
            }
            16 => {
                v___x_3995_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_3978_);
                v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
                lean_inc(v_a_3996_);
                lean_dec_ref(v___x_3995_);
                v___x_3997_ = lean_st_ref_get(v___y_3978_);
                v_env_3998_ = lean_ctor_get(v___x_3997_, 0);
                lean_inc_ref(v_env_3998_);
                lean_dec(v___x_3997_);
                v_ref_3999_ = l_Lean_replaceRef(v___y_3977_, v___y_3977_);
                lean_inc_ref(v___y_3994_);
                lean_inc(v___y_3991_);
                lean_inc(v___y_3979_);
                lean_inc(v___y_3984_);
                lean_inc(v___y_3987_);
                lean_inc(v___y_3975_);
                lean_inc(v___y_3970_);
                lean_inc(v___y_3982_);
                lean_inc(v_ref_3999_);
                lean_inc(v___y_3985_);
                lean_inc_ref_n(v___y_3989_, 2);
                lean_inc_ref(v___y_3993_);
                lean_inc_ref(v___y_3980_);
                v___x_4000_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4000_, 0, v___y_3980_);
                lean_ctor_set(v___x_4000_, 1, v___y_3993_);
                lean_ctor_set(v___x_4000_, 2, v___y_3989_);
                lean_ctor_set(v___x_4000_, 3, v___y_3985_);
                lean_ctor_set(v___x_4000_, 4, v___y_3981_);
                lean_ctor_set(v___x_4000_, 5, v_ref_3999_);
                lean_ctor_set(v___x_4000_, 6, v___y_3982_);
                lean_ctor_set(v___x_4000_, 7, v___y_3970_);
                lean_ctor_set(v___x_4000_, 8, v___y_3975_);
                lean_ctor_set(v___x_4000_, 9, v___y_3987_);
                lean_ctor_set(v___x_4000_, 10, v___y_3984_);
                lean_ctor_set(v___x_4000_, 11, v___y_3979_);
                lean_ctor_set(v___x_4000_, 12, v___y_3991_);
                lean_ctor_set(v___x_4000_, 13, v___y_3994_);
                lean_ctor_set_uint8(
                    v___x_4000_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_3968_,
                );
                lean_ctor_set_uint8(
                    v___x_4000_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v___y_3988_,
                );
                v___x_4001_ = l_Lean_MessageData_ofLevel(v___y_3976_);
                v___x_4002_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once), _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
                v___x_4003_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4003_, 0, v___x_4001_);
                lean_ctor_set(v___x_4003_, 1, v___x_4002_);
                v___x_4004_ = l_Lean_MessageData_ofLevel(v___y_3972_);
                v___x_4005_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4005_, 0, v___x_4003_);
                lean_ctor_set(v___x_4005_, 1, v___x_4004_);
                v___x_4006_ = l_Lean_Meta_isLevelDefEqAuxImpl___closed__6;
                v___x_4007_ = 0;
                v___x_4008_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(
                    v___y_3989_,
                    v___x_4006_,
                    v___x_4007_,
                );
                v___x_4009_ = l_Lean_diagnostics;
                v___x_4010_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(
                    v___x_4008_,
                    v___x_4009_,
                );
                v___x_4011_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3998_);
                lean_dec_ref(v_env_3998_);
                if v___x_4011_ == 0 {
                    if v___x_4010_ == 0 {
                        lean_inc(v___y_3978_);
                        v___y_3822_ = v___y_3983_;
                        v___y_3823_ = v___x_4005_;
                        v___y_3824_ = v___y_3986_;
                        v___y_3825_ = v___y_3971_;
                        v___y_3826_ = v___y_3969_;
                        v___y_3827_ = v___y_3973_;
                        v___y_3828_ = v___y_3989_;
                        v___y_3829_ = v___x_4008_;
                        v___y_3830_ = v___y_3990_;
                        v___y_3831_ = v___x_4010_;
                        v___y_3832_ = v___y_3974_;
                        v___y_3833_ = v_a_3996_;
                        v___y_3834_ = v___y_3992_;
                        v___y_3835_ = v___x_4000_;
                        v___y_3836_ = v___y_3977_;
                        v___y_3837_ = v___y_3978_;
                        v_fileName_3838_ = v___y_3980_;
                        v_fileMap_3839_ = v___y_3993_;
                        v_currRecDepth_3840_ = v___y_3985_;
                        v_ref_3841_ = v_ref_3999_;
                        v_currNamespace_3842_ = v___y_3982_;
                        v_openDecls_3843_ = v___y_3970_;
                        v_initHeartbeats_3844_ = v___y_3975_;
                        v_maxHeartbeats_3845_ = v___y_3987_;
                        v_quotContext_3846_ = v___y_3984_;
                        v_currMacroScope_3847_ = v___y_3979_;
                        v_cancelTk_x3f_3848_ = v___y_3991_;
                        v_suppressElabErrors_3849_ = v___y_3988_;
                        v_inheritedTraceOptions_3850_ = v___y_3994_;
                        v___y_3851_ = v___y_3978_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_ref_3999_);
                        lean_dec_ref(v___y_3994_);
                        lean_dec_ref(v___y_3993_);
                        lean_dec(v___y_3991_);
                        lean_dec(v___y_3987_);
                        lean_dec(v___y_3985_);
                        lean_dec(v___y_3984_);
                        lean_dec(v___y_3982_);
                        lean_dec_ref(v___y_3980_);
                        lean_dec(v___y_3979_);
                        lean_dec(v___y_3975_);
                        lean_dec(v___y_3970_);
                        v___y_3930_ = v___y_3983_;
                        v___y_3931_ = v___x_4005_;
                        v___y_3932_ = v___y_3986_;
                        v___y_3933_ = v___y_3971_;
                        v___y_3934_ = v___y_3969_;
                        v___y_3935_ = v___y_3973_;
                        v___y_3936_ = v___y_3989_;
                        v___y_3937_ = v___x_4008_;
                        v___y_3938_ = v___y_3990_;
                        v___y_3939_ = v___y_3974_;
                        v___y_3940_ = v___x_4010_;
                        v___y_3941_ = v_a_3996_;
                        v___y_3942_ = v___y_3992_;
                        v___y_3943_ = v___x_4000_;
                        v___y_3944_ = v___y_3977_;
                        v___y_3945_ = v___y_3978_;
                        v___y_3946_ = v___x_4011_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec(v_ref_3999_);
                    lean_dec_ref(v___y_3994_);
                    lean_dec_ref(v___y_3993_);
                    lean_dec(v___y_3991_);
                    lean_dec(v___y_3987_);
                    lean_dec(v___y_3985_);
                    lean_dec(v___y_3984_);
                    lean_dec(v___y_3982_);
                    lean_dec_ref(v___y_3980_);
                    lean_dec(v___y_3979_);
                    lean_dec(v___y_3975_);
                    lean_dec(v___y_3970_);
                    v___y_3930_ = v___y_3983_;
                    v___y_3931_ = v___x_4005_;
                    v___y_3932_ = v___y_3986_;
                    v___y_3933_ = v___y_3971_;
                    v___y_3934_ = v___y_3969_;
                    v___y_3935_ = v___y_3973_;
                    v___y_3936_ = v___y_3989_;
                    v___y_3937_ = v___x_4008_;
                    v___y_3938_ = v___y_3990_;
                    v___y_3939_ = v___y_3974_;
                    v___y_3940_ = v___x_4010_;
                    v___y_3941_ = v_a_3996_;
                    v___y_3942_ = v___y_3992_;
                    v___y_3943_ = v___x_4000_;
                    v___y_3944_ = v___y_3977_;
                    v___y_3945_ = v___y_3978_;
                    v___y_3946_ = v___x_4010_;
                    state = 13;
                    continue;
                }
            }
            17 => {
                v_options_4019_ = lean_ctor_get(v___y_4017_, 2);
                v_fileName_4020_ = lean_ctor_get(v___y_4017_, 0);
                v_fileMap_4021_ = lean_ctor_get(v___y_4017_, 1);
                v_currRecDepth_4022_ = lean_ctor_get(v___y_4017_, 3);
                v_maxRecDepth_4023_ = lean_ctor_get(v___y_4017_, 4);
                v_ref_4024_ = lean_ctor_get(v___y_4017_, 5);
                v_currNamespace_4025_ = lean_ctor_get(v___y_4017_, 6);
                v_openDecls_4026_ = lean_ctor_get(v___y_4017_, 7);
                v_initHeartbeats_4027_ = lean_ctor_get(v___y_4017_, 8);
                v_maxHeartbeats_4028_ = lean_ctor_get(v___y_4017_, 9);
                v_quotContext_4029_ = lean_ctor_get(v___y_4017_, 10);
                v_currMacroScope_4030_ = lean_ctor_get(v___y_4017_, 11);
                v_diag_4031_ = lean_ctor_get_uint8(
                    v___y_4017_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4032_ = lean_ctor_get(v___y_4017_, 12);
                v_suppressElabErrors_4033_ = lean_ctor_get_uint8(
                    v___y_4017_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4034_ = lean_ctor_get(v___y_4017_, 13);
                v_hasTrace_4035_ = lean_ctor_get_uint8(
                    v_options_4019_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_4036_ =
                    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4;
                v___x_4037_ =
                    l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5;
                v___x_4038_ = l_Lean_Level_getLevelOffset(v_lhs_4013_);
                v___x_4039_ = l_Lean_Level_getLevelOffset(v_rhs_4014_);
                v___x_4040_ = lean_level_eq(v___x_4038_, v___x_4039_);
                lean_dec(v___x_4039_);
                lean_dec(v___x_4038_);
                v___x_4041_ = 1;
                v___x_4042_ = lean_box((v___x_4040_) as usize);
                v___x_4043_ = lean_box((v___x_4041_) as usize);
                lean_inc(v_rhs_4014_);
                lean_inc(v_lhs_4013_);
                v___y_4044_ = lean_alloc_closure(
                    l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    6,
                );
                lean_closure_set(v___y_4044_, 0, v___x_4042_);
                lean_closure_set(v___y_4044_, 1, v_lhs_4013_);
                lean_closure_set(v___y_4044_, 2, v_rhs_4014_);
                lean_closure_set(v___y_4044_, 3, v___x_4036_);
                lean_closure_set(v___y_4044_, 4, v___x_4037_);
                lean_closure_set(v___y_4044_, 5, v___x_4043_);
                if v_hasTrace_4035_ == 0 {
                    lean_dec_ref(v___y_4044_);
                    v___x_4045_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(
                        v___x_4040_,
                        v_lhs_4013_,
                        v_rhs_4014_,
                        v___x_4036_,
                        v___x_4037_,
                        v___x_4041_,
                        v___y_4015_,
                        v___y_4016_,
                        v___y_4017_,
                        v___y_4018_,
                    );
                    lean_dec(v___y_4018_);
                    lean_dec_ref(v___y_4017_);
                    lean_dec(v___y_4016_);
                    lean_dec_ref(v___y_4015_);
                    return v___x_4045_;
                } else {
                    v___x_4046_ = l_Lean_Meta_isLevelDefEqAuxImpl___closed__7;
                    v___x_4047_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1;
                    v___x_4048_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once),
                        _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8,
                    );
                    v___x_4049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4034_,
                        v_options_4019_,
                        v___x_4048_,
                    );
                    if v___x_4049_ == 0 {
                        v___x_4050_ = l_Lean_trace_profiler;
                        v___x_4051_ =
                            l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(
                                v_options_4019_,
                                v___x_4050_,
                            );
                        if v___x_4051_ == 0 {
                            lean_dec_ref(v___y_4044_);
                            v___x_4052_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(
                                v___x_4040_,
                                v_lhs_4013_,
                                v_rhs_4014_,
                                v___x_4036_,
                                v___x_4037_,
                                v___x_4041_,
                                v___y_4015_,
                                v___y_4016_,
                                v___y_4017_,
                                v___y_4018_,
                            );
                            lean_dec(v___y_4018_);
                            lean_dec_ref(v___y_4017_);
                            lean_dec(v___y_4016_);
                            lean_dec_ref(v___y_4015_);
                            return v___x_4052_;
                        } else {
                            lean_inc_ref(v_inheritedTraceOptions_4034_);
                            lean_inc(v_cancelTk_x3f_4032_);
                            lean_inc(v_currMacroScope_4030_);
                            lean_inc(v_quotContext_4029_);
                            lean_inc(v_maxHeartbeats_4028_);
                            lean_inc(v_initHeartbeats_4027_);
                            lean_inc(v_openDecls_4026_);
                            lean_inc(v_currNamespace_4025_);
                            lean_inc(v_ref_4024_);
                            lean_inc(v_maxRecDepth_4023_);
                            lean_inc(v_currRecDepth_4022_);
                            lean_inc_ref(v_fileMap_4021_);
                            lean_inc_ref(v_fileName_4020_);
                            lean_inc_ref(v_options_4019_);
                            v___y_3968_ = v_diag_4031_;
                            v___y_3969_ = v___x_4046_;
                            v___y_3970_ = v_openDecls_4026_;
                            v___y_3971_ = v___y_4016_;
                            v___y_3972_ = v_rhs_4014_;
                            v___y_3973_ = v___x_4041_;
                            v___y_3974_ = v___y_4017_;
                            v___y_3975_ = v_initHeartbeats_4027_;
                            v___y_3976_ = v_lhs_4013_;
                            v___y_3977_ = v_ref_4024_;
                            v___y_3978_ = v___y_4018_;
                            v___y_3979_ = v_currMacroScope_4030_;
                            v___y_3980_ = v_fileName_4020_;
                            v___y_3981_ = v_maxRecDepth_4023_;
                            v___y_3982_ = v_currNamespace_4025_;
                            v___y_3983_ = v___x_4047_;
                            v___y_3984_ = v_quotContext_4029_;
                            v___y_3985_ = v_currRecDepth_4022_;
                            v___y_3986_ = v___x_4049_;
                            v___y_3987_ = v_maxHeartbeats_4028_;
                            v___y_3988_ = v_suppressElabErrors_4033_;
                            v___y_3989_ = v_options_4019_;
                            v___y_3990_ = v___y_4015_;
                            v___y_3991_ = v_cancelTk_x3f_4032_;
                            v___y_3992_ = v___y_4044_;
                            v___y_3993_ = v_fileMap_4021_;
                            v___y_3994_ = v_inheritedTraceOptions_4034_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_inc_ref(v_inheritedTraceOptions_4034_);
                        lean_inc(v_cancelTk_x3f_4032_);
                        lean_inc(v_currMacroScope_4030_);
                        lean_inc(v_quotContext_4029_);
                        lean_inc(v_maxHeartbeats_4028_);
                        lean_inc(v_initHeartbeats_4027_);
                        lean_inc(v_openDecls_4026_);
                        lean_inc(v_currNamespace_4025_);
                        lean_inc(v_ref_4024_);
                        lean_inc(v_maxRecDepth_4023_);
                        lean_inc(v_currRecDepth_4022_);
                        lean_inc_ref(v_fileMap_4021_);
                        lean_inc_ref(v_fileName_4020_);
                        lean_inc_ref(v_options_4019_);
                        v___y_3968_ = v_diag_4031_;
                        v___y_3969_ = v___x_4046_;
                        v___y_3970_ = v_openDecls_4026_;
                        v___y_3971_ = v___y_4016_;
                        v___y_3972_ = v_rhs_4014_;
                        v___y_3973_ = v___x_4041_;
                        v___y_3974_ = v___y_4017_;
                        v___y_3975_ = v_initHeartbeats_4027_;
                        v___y_3976_ = v_lhs_4013_;
                        v___y_3977_ = v_ref_4024_;
                        v___y_3978_ = v___y_4018_;
                        v___y_3979_ = v_currMacroScope_4030_;
                        v___y_3980_ = v_fileName_4020_;
                        v___y_3981_ = v_maxRecDepth_4023_;
                        v___y_3982_ = v_currNamespace_4025_;
                        v___y_3983_ = v___x_4047_;
                        v___y_3984_ = v_quotContext_4029_;
                        v___y_3985_ = v_currRecDepth_4022_;
                        v___y_3986_ = v___x_4049_;
                        v___y_3987_ = v_maxHeartbeats_4028_;
                        v___y_3988_ = v_suppressElabErrors_4033_;
                        v___y_3989_ = v_options_4019_;
                        v___y_3990_ = v___y_4015_;
                        v___y_3991_ = v_cancelTk_x3f_4032_;
                        v___y_3992_ = v___y_4044_;
                        v___y_3993_ = v_fileMap_4021_;
                        v___y_3994_ = v_inheritedTraceOptions_4034_;
                        state = 16;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isLevelDefEqAuxImpl___boxed(
    mut v_x_4056_: *mut LeanObject,
    mut v_x_4057_: *mut LeanObject,
    mut v_a_4058_: *mut LeanObject,
    mut v_a_4059_: *mut LeanObject,
    mut v_a_4060_: *mut LeanObject,
    mut v_a_4061_: *mut LeanObject,
    mut v_a_4062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4063_: *mut LeanObject = core::ptr::null_mut();
    v_res_4063_ = lean_is_level_def_eq(
        v_x_4056_, v_x_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_,
    );
    return v_res_4063_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(
    mut v_00_u03b1_4064_: *mut LeanObject,
    mut v_x_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
    mut v___y_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_x_4065_);
    return v___x_4071_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(
    mut v_00_u03b1_4072_: *mut LeanObject,
    mut v_x_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
    mut v___y_4075_: *mut LeanObject,
    mut v___y_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4079_: *mut LeanObject = core::ptr::null_mut();
    v_res_4079_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_00_u03b1_4072_, v_x_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
    lean_dec(v___y_4077_);
    lean_dec_ref(v___y_4076_);
    lean_dec(v___y_4075_);
    lean_dec_ref(v___y_4074_);
    return v_res_4079_;
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    v___x_4136_ = l_Lean_Meta_isLevelDefEqAuxImpl___closed__7;
    v___x_4137_ = 0;
    v___x_4138_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_;
    v___x_4139_ = l_Lean_registerTraceClass(v___x_4136_, v___x_4137_, v___x_4138_);
    if lean_obj_tag(v___x_4139_) == 0 {
        let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4141_: u8 = 0;
        let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_4139_, 1);
        v___x_4140_ =
            l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
        v___x_4141_ = 1;
        v___x_4142_ = l_Lean_registerTraceClass(v___x_4140_, v___x_4141_, v___x_4138_);
        return v___x_4142_;
    } else {
        return v___x_4139_;
    }
}
pub unsafe fn l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(
    mut v_a_4143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4144_: *mut LeanObject = core::ptr::null_mut();
    v_res_4144_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
    return v_res_4144_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_LevelDefEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasAssignableMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_LevelDefEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_LevelDefEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_HasAssignableMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LevelDefEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_LevelDefEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_LevelDefEq(builtin);
}
