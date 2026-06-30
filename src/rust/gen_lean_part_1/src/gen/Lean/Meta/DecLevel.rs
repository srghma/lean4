// Lean compiler output
// Module: Lean.Meta.DecLevel
// Imports: Lean.Meta.InferType
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_instInhabitedForall___redArg___lam__0___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_succ___override, l_Lean_instBEqLevelMVarId_beq,
    l_Lean_instHashableLevelMVarId_hash, l_Lean_mkLevelMVar, l_Lean_mkLevelMax_x27,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofLevel, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_LMVarId_isReadOnly, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_mkFreshLevelMVar, l_Lean_Meta_normalizeLevel,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, l_Lean_Meta_getLevel, runtime_initialize_Lean_Meta_InferType,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
pub static l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value
        ) as *mut leanh::LeanObject,
        142734480563613395 as *mut leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1_value
        ) as *mut leanh::LeanObject,
        7797271807932843206 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2_value
        ) as *mut leanh::LeanObject,
        14740709623910891990 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
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
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4_value
        ) as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 101, 99, 65, 117, 120, 63, 44, 32, 0],
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 101, 99, 76, 101, 118, 101, 108, 0,
    ],
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
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
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68,
        101, 99, 76, 101, 118, 101, 108, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46,
        100, 101, 99, 65, 117, 120, 63, 0,
    ],
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_decLevel___closed__0_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108,
            101, 118, 101, 108, 44, 32, 0,
        ],
    };
static mut l_Lean_Meta_decLevel___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_decLevel___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_decLevel___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_decLevel___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_decLevel___closed__2_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            32, 105, 115, 32, 110, 111, 116, 32, 103, 114, 101, 97, 116, 101, 114, 32, 116, 104,
            97, 110, 32, 48, 0,
        ],
    };
static mut l_Lean_Meta_decLevel___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_decLevel___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_decLevel___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_decLevel___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 101, 99, 76, 101, 118, 101, 108, 0]};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15053436033843189845 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,17111767716225397952 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5736393772439215353 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value) as *mut leanh::LeanObject,25828639650662505 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17304663082519133680 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17645492162070676209 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11786942372265145012 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value) as *mut leanh::LeanObject,18085474514652296296 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11994573517353298051 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(
    mut v_msg_901_: *mut leanh::LeanObject,
    mut v___y_902_: u8,
    mut v___y_903_: *mut leanh::LeanObject,
    mut v___y_904_: *mut leanh::LeanObject,
    mut v___y_905_: *mut leanh::LeanObject,
    mut v___y_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7834__overap_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_908_ =
        l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0;
    v___f_909_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_909_, 0, v___f_908_);
    v___x_7834__overap_910_ = lean_panic_fn_borrowed(v___f_909_, v_msg_901_);
    leanh::lean_dec_ref(v___f_909_);
    v___x_911_ = leanh::lean_box((v___y_902_) as usize);
    leanh::lean_inc(v___y_906_);
    leanh::lean_inc_ref(v___y_905_);
    leanh::lean_inc(v___y_904_);
    leanh::lean_inc_ref(v___y_903_);
    v___x_912_ = leanh::lean_apply_6(
        v___x_7834__overap_910_,
        v___x_911_,
        v___y_903_,
        v___y_904_,
        v___y_905_,
        v___y_906_,
        leanh::lean_box(0),
    );
    return v___x_912_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___boxed(
    mut v_msg_913_: *mut leanh::LeanObject,
    mut v___y_914_: *mut leanh::LeanObject,
    mut v___y_915_: *mut leanh::LeanObject,
    mut v___y_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8699__boxed_920_: u8 = 0;
    let mut v_res_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_8699__boxed_920_ = (leanh::lean_unbox(v___y_914_) as u8);
    v_res_921_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(
        v_msg_913_,
        v___y_8699__boxed_920_,
        v___y_915_,
        v___y_916_,
        v___y_917_,
        v___y_918_,
    );
    leanh::lean_dec(v___y_918_);
    leanh::lean_dec_ref(v___y_917_);
    leanh::lean_dec(v___y_916_);
    leanh::lean_dec_ref(v___y_915_);
    return v_res_921_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(
    mut v_msgData_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
    mut v___y_925_: *mut leanh::LeanObject,
    mut v___y_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_928_ = lean_st_ref_get(v___y_926_);
    v_env_929_ = leanh::lean_ctor_get(v___x_928_, 0);
    leanh::lean_inc_ref(v_env_929_);
    leanh::lean_dec(v___x_928_);
    v___x_930_ = lean_st_ref_get(v___y_924_);
    v_mctx_931_ = leanh::lean_ctor_get(v___x_930_, 0);
    leanh::lean_inc_ref(v_mctx_931_);
    leanh::lean_dec(v___x_930_);
    v_lctx_932_ = leanh::lean_ctor_get(v___y_923_, 2);
    v_options_933_ = leanh::lean_ctor_get(v___y_925_, 2);
    leanh::lean_inc_ref(v_options_933_);
    leanh::lean_inc_ref(v_lctx_932_);
    v___x_934_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_934_, 0, v_env_929_);
    leanh::lean_ctor_set(v___x_934_, 1, v_mctx_931_);
    leanh::lean_ctor_set(v___x_934_, 2, v_lctx_932_);
    leanh::lean_ctor_set(v___x_934_, 3, v_options_933_);
    v___x_935_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_935_, 0, v___x_934_);
    leanh::lean_ctor_set(v___x_935_, 1, v_msgData_922_);
    v___x_936_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_936_, 0, v___x_935_);
    return v___x_936_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4___boxed(
    mut v_msgData_937_: *mut leanh::LeanObject,
    mut v___y_938_: *mut leanh::LeanObject,
    mut v___y_939_: *mut leanh::LeanObject,
    mut v___y_940_: *mut leanh::LeanObject,
    mut v___y_941_: *mut leanh::LeanObject,
    mut v___y_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msgData_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
    leanh::lean_dec(v___y_941_);
    leanh::lean_dec_ref(v___y_940_);
    leanh::lean_dec(v___y_939_);
    leanh::lean_dec_ref(v___y_938_);
    return v_res_943_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: f64 = 0.0;
    v___x_944_ = leanh::lean_unsigned_to_nat(0);
    v___x_945_ = lean_float_of_nat(v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(
    mut v_cls_949_: *mut leanh::LeanObject,
    mut v_msg_950_: *mut leanh::LeanObject,
    mut v___y_951_: *mut leanh::LeanObject,
    mut v___y_952_: *mut leanh::LeanObject,
    mut v___y_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_974_: u8 = 0;
    let mut v_tid_975_: u64 = 0;
    let mut v_traces_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_979_: u8 = 0;
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: f64 = 0.0;
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1000_: u8 = 0;
    let mut v_isSharedCheck_1001_: u8 = 0;
    let mut v_isSharedCheck_1002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_956_ = leanh::lean_ctor_get(v___y_953_, 5);
                v___x_957_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
                v_a_958_ = leanh::lean_ctor_get(v___x_957_, 0);
                v_isSharedCheck_1002_ = (!leanh::lean_is_exclusive(v___x_957_)) as u8;
                if v_isSharedCheck_1002_ == 0 {
                    v___x_960_ = v___x_957_;
                    v_isShared_961_ = v_isSharedCheck_1002_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_958_);
                    leanh::lean_dec(v___x_957_);
                    v___x_960_ = leanh::lean_box(0);
                    v_isShared_961_ = v_isSharedCheck_1002_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_962_ = lean_st_ref_take(v___y_954_);
                v_traceState_963_ = leanh::lean_ctor_get(v___x_962_, 4);
                v_env_964_ = leanh::lean_ctor_get(v___x_962_, 0);
                v_nextMacroScope_965_ = leanh::lean_ctor_get(v___x_962_, 1);
                v_ngen_966_ = leanh::lean_ctor_get(v___x_962_, 2);
                v_auxDeclNGen_967_ = leanh::lean_ctor_get(v___x_962_, 3);
                v_cache_968_ = leanh::lean_ctor_get(v___x_962_, 5);
                v_messages_969_ = leanh::lean_ctor_get(v___x_962_, 6);
                v_infoState_970_ = leanh::lean_ctor_get(v___x_962_, 7);
                v_snapshotTasks_971_ = leanh::lean_ctor_get(v___x_962_, 8);
                v_isSharedCheck_1001_ = (!leanh::lean_is_exclusive(v___x_962_)) as u8;
                if v_isSharedCheck_1001_ == 0 {
                    v___x_973_ = v___x_962_;
                    v_isShared_974_ = v_isSharedCheck_1001_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_971_);
                    leanh::lean_inc(v_infoState_970_);
                    leanh::lean_inc(v_messages_969_);
                    leanh::lean_inc(v_cache_968_);
                    leanh::lean_inc(v_traceState_963_);
                    leanh::lean_inc(v_auxDeclNGen_967_);
                    leanh::lean_inc(v_ngen_966_);
                    leanh::lean_inc(v_nextMacroScope_965_);
                    leanh::lean_inc(v_env_964_);
                    leanh::lean_dec(v___x_962_);
                    v___x_973_ = leanh::lean_box(0);
                    v_isShared_974_ = v_isSharedCheck_1001_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_975_ = leanh::lean_ctor_get_uint64(
                    v_traceState_963_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_976_ = leanh::lean_ctor_get(v_traceState_963_, 0);
                v_isSharedCheck_1000_ = (!leanh::lean_is_exclusive(v_traceState_963_)) as u8;
                if v_isSharedCheck_1000_ == 0 {
                    v___x_978_ = v_traceState_963_;
                    v_isShared_979_ = v_isSharedCheck_1000_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_976_);
                    leanh::lean_dec(v_traceState_963_);
                    v___x_978_ = leanh::lean_box(0);
                    v_isShared_979_ = v_isSharedCheck_1000_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_980_ = leanh::lean_box(0);
                v___x_981_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0);
                v___x_982_ = 0;
                v___x_983_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1;
                v___x_984_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_984_, 0, v_cls_949_);
                leanh::lean_ctor_set(v___x_984_, 1, v___x_980_);
                leanh::lean_ctor_set(v___x_984_, 2, v___x_983_);
                leanh::lean_ctor_set_float(
                    v___x_984_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_981_,
                );
                leanh::lean_ctor_set_float(
                    v___x_984_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_981_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_984_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_982_,
                );
                v___x_985_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2;
                v___x_986_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
                leanh::lean_ctor_set(v___x_986_, 1, v_a_958_);
                leanh::lean_ctor_set(v___x_986_, 2, v___x_985_);
                leanh::lean_inc(v_ref_956_);
                v___x_987_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_987_, 0, v_ref_956_);
                leanh::lean_ctor_set(v___x_987_, 1, v___x_986_);
                v___x_988_ = l_Lean_PersistentArray_push___redArg(v_traces_976_, v___x_987_);
                if v_isShared_979_ == 0 {
                    leanh::lean_ctor_set(v___x_978_, 0, v___x_988_);
                    v___x_990_ = v___x_978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_999_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_988_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_999_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_975_,
                    );
                    v___x_990_ = v_reuseFailAlloc_999_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_974_ == 0 {
                    leanh::lean_ctor_set(v___x_973_, 4, v___x_990_);
                    v___x_992_ = v___x_973_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 0, v_env_964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 1, v_nextMacroScope_965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 2, v_ngen_966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 3, v_auxDeclNGen_967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 4, v___x_990_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 5, v_cache_968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 6, v_messages_969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 7, v_infoState_970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 8, v_snapshotTasks_971_);
                    v___x_992_ = v_reuseFailAlloc_998_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_993_ = lean_st_ref_set(v___y_954_, v___x_992_);
                v___x_994_ = leanh::lean_box(0);
                if v_isShared_961_ == 0 {
                    leanh::lean_ctor_set(v___x_960_, 0, v___x_994_);
                    v___x_996_ = v___x_960_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___boxed(
    mut v_cls_1003_: *mut leanh::LeanObject,
    mut v_msg_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_1003_, v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
    leanh::lean_dec(v___y_1008_);
    leanh::lean_dec_ref(v___y_1007_);
    leanh::lean_dec(v___y_1006_);
    leanh::lean_dec_ref(v___y_1005_);
    return v_res_1010_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(
    mut v_x_1011_: *mut leanh::LeanObject,
    mut v_x_1012_: *mut leanh::LeanObject,
    mut v_x_1013_: *mut leanh::LeanObject,
    mut v_x_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1015_ = leanh::lean_ctor_get(v_x_1011_, 0);
                v_vs_1016_ = leanh::lean_ctor_get(v_x_1011_, 1);
                v_isSharedCheck_1040_ = (!leanh::lean_is_exclusive(v_x_1011_)) as u8;
                if v_isSharedCheck_1040_ == 0 {
                    v___x_1018_ = v_x_1011_;
                    v_isShared_1019_ = v_isSharedCheck_1040_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1016_);
                    leanh::lean_inc(v_ks_1015_);
                    leanh::lean_dec(v_x_1011_);
                    v___x_1018_ = leanh::lean_box(0);
                    v_isShared_1019_ = v_isSharedCheck_1040_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1020_ = lean_array_get_size(v_ks_1015_);
                v___x_1021_ = lean_nat_dec_lt(v_x_1012_, v___x_1020_);
                if v___x_1021_ == 0 {
                    leanh::lean_dec(v_x_1012_);
                    v___x_1022_ = lean_array_push(v_ks_1015_, v_x_1013_);
                    v___x_1023_ = lean_array_push(v_vs_1016_, v_x_1014_);
                    if v_isShared_1019_ == 0 {
                        leanh::lean_ctor_set(v___x_1018_, 1, v___x_1023_);
                        leanh::lean_ctor_set(v___x_1018_, 0, v___x_1022_);
                        v___x_1025_ = v___x_1018_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1026_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1022_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_1023_);
                        v___x_1025_ = v_reuseFailAlloc_1026_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1027_ = lean_array_fget_borrowed(v_ks_1015_, v_x_1012_);
                    v___x_1028_ = l_Lean_instBEqLevelMVarId_beq(v_x_1013_, v_k_x27_1027_);
                    if v___x_1028_ == 0 {
                        if v_isShared_1019_ == 0 {
                            v___x_1030_ = v___x_1018_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1034_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_ks_1015_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_vs_1016_);
                            v___x_1030_ = v_reuseFailAlloc_1034_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1035_ = lean_array_fset(v_ks_1015_, v_x_1012_, v_x_1013_);
                        v___x_1036_ = lean_array_fset(v_vs_1016_, v_x_1012_, v_x_1014_);
                        leanh::lean_dec(v_x_1012_);
                        if v_isShared_1019_ == 0 {
                            leanh::lean_ctor_set(v___x_1018_, 1, v___x_1036_);
                            leanh::lean_ctor_set(v___x_1018_, 0, v___x_1035_);
                            v___x_1038_ = v___x_1018_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1039_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1035_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
                            v___x_1038_ = v_reuseFailAlloc_1039_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1025_;
            }
            3 => {
                v___x_1031_ = leanh::lean_unsigned_to_nat(1);
                v___x_1032_ = lean_nat_add(v_x_1012_, v___x_1031_);
                leanh::lean_dec(v_x_1012_);
                v_x_1011_ = v___x_1030_;
                v_x_1012_ = v___x_1032_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(
    mut v_n_1041_: *mut leanh::LeanObject,
    mut v_k_1042_: *mut leanh::LeanObject,
    mut v_v_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = leanh::lean_unsigned_to_nat(0);
    v___x_1045_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_n_1041_, v___x_1044_, v_k_1042_, v_v_1043_);
    return v___x_1045_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_1046_: usize = 0;
    let mut v___x_1047_: usize = 0;
    let mut v___x_1048_: usize = 0;
    v___x_1046_ = 5usize;
    v___x_1047_ = 1usize;
    v___x_1048_ = lean_usize_shift_left(v___x_1047_, v___x_1046_);
    return v___x_1048_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: usize = 0;
    let mut v___x_1051_: usize = 0;
    v___x_1049_ = 1usize;
    v___x_1050_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0);
    v___x_1051_ = lean_usize_sub(v___x_1050_, v___x_1049_);
    return v___x_1051_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1052_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_x_1053_: *mut leanh::LeanObject,
    mut v_x_1054_: usize,
    mut v_x_1055_: usize,
    mut v_x_1056_: *mut leanh::LeanObject,
    mut v_x_1057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: usize = 0;
    let mut v___x_1060_: usize = 0;
    let mut v___x_1061_: usize = 0;
    let mut v___x_1062_: usize = 0;
    let mut v_j_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: u8 = 0;
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1068_: u8 = 0;
    let mut v_v_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1082_: u8 = 0;
    let mut v___x_1083_: u8 = 0;
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v_node_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: usize = 0;
    let mut v___x_1095_: usize = 0;
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1100_: u8 = 0;
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut v_unused_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1108_: u8 = 0;
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1113_: u8 = 0;
    let mut v_ks_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: usize = 0;
    let mut v___x_1120_: u8 = 0;
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: u8 = 0;
    let mut v_reuseFailAlloc_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1053_) == 0 {
                    v_es_1058_ = leanh::lean_ctor_get(v_x_1053_, 0);
                    v___x_1059_ = 5usize;
                    v___x_1060_ = 1usize;
                    v___x_1061_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1);
                    v___x_1062_ = lean_usize_land(v_x_1054_, v___x_1061_);
                    v_j_1063_ = lean_usize_to_nat(v___x_1062_);
                    v___x_1064_ = lean_array_get_size(v_es_1058_);
                    v___x_1065_ = lean_nat_dec_lt(v_j_1063_, v___x_1064_);
                    if v___x_1065_ == 0 {
                        leanh::lean_dec(v_j_1063_);
                        leanh::lean_dec(v_x_1057_);
                        leanh::lean_dec(v_x_1056_);
                        return v_x_1053_;
                    } else {
                        leanh::lean_inc_ref(v_es_1058_);
                        v_isSharedCheck_1102_ = (!leanh::lean_is_exclusive(v_x_1053_)) as u8;
                        if v_isSharedCheck_1102_ == 0 {
                            v_unused_1103_ = leanh::lean_ctor_get(v_x_1053_, 0);
                            leanh::lean_dec(v_unused_1103_);
                            v___x_1067_ = v_x_1053_;
                            v_isShared_1068_ = v_isSharedCheck_1102_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1053_);
                            v___x_1067_ = leanh::lean_box(0);
                            v_isShared_1068_ = v_isSharedCheck_1102_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1104_ = leanh::lean_ctor_get(v_x_1053_, 0);
                    v_vs_1105_ = leanh::lean_ctor_get(v_x_1053_, 1);
                    v_isSharedCheck_1125_ = (!leanh::lean_is_exclusive(v_x_1053_)) as u8;
                    if v_isSharedCheck_1125_ == 0 {
                        v___x_1107_ = v_x_1053_;
                        v_isShared_1108_ = v_isSharedCheck_1125_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1105_);
                        leanh::lean_inc(v_ks_1104_);
                        leanh::lean_dec(v_x_1053_);
                        v___x_1107_ = leanh::lean_box(0);
                        v_isShared_1108_ = v_isSharedCheck_1125_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1069_ = lean_array_fget(v_es_1058_, v_j_1063_);
                v___x_1070_ = leanh::lean_box(0);
                v_xs_x27_1071_ = lean_array_fset(v_es_1058_, v_j_1063_, v___x_1070_);
                match leanh::lean_obj_tag(v_v_1069_) {
                    0 => {
                        v_key_1078_ = leanh::lean_ctor_get(v_v_1069_, 0);
                        v_val_1079_ = leanh::lean_ctor_get(v_v_1069_, 1);
                        v_isSharedCheck_1089_ = (!leanh::lean_is_exclusive(v_v_1069_)) as u8;
                        if v_isSharedCheck_1089_ == 0 {
                            v___x_1081_ = v_v_1069_;
                            v_isShared_1082_ = v_isSharedCheck_1089_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1079_);
                            leanh::lean_inc(v_key_1078_);
                            leanh::lean_dec(v_v_1069_);
                            v___x_1081_ = leanh::lean_box(0);
                            v_isShared_1082_ = v_isSharedCheck_1089_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1090_ = leanh::lean_ctor_get(v_v_1069_, 0);
                        v_isSharedCheck_1100_ = (!leanh::lean_is_exclusive(v_v_1069_)) as u8;
                        if v_isSharedCheck_1100_ == 0 {
                            v___x_1092_ = v_v_1069_;
                            v_isShared_1093_ = v_isSharedCheck_1100_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1090_);
                            leanh::lean_dec(v_v_1069_);
                            v___x_1092_ = leanh::lean_box(0);
                            v_isShared_1093_ = v_isSharedCheck_1100_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1101_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1101_, 0, v_x_1056_);
                        leanh::lean_ctor_set(v___x_1101_, 1, v_x_1057_);
                        v___y_1073_ = v___x_1101_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1074_ = lean_array_fset(v_xs_x27_1071_, v_j_1063_, v___y_1073_);
                leanh::lean_dec(v_j_1063_);
                if v_isShared_1068_ == 0 {
                    leanh::lean_ctor_set(v___x_1067_, 0, v___x_1074_);
                    v___x_1076_ = v___x_1067_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1077_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
                    v___x_1076_ = v_reuseFailAlloc_1077_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1076_;
            }
            4 => {
                v___x_1083_ = l_Lean_instBEqLevelMVarId_beq(v_x_1056_, v_key_1078_);
                if v___x_1083_ == 0 {
                    leanh::lean_del_object(v___x_1081_);
                    v___x_1084_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1078_,
                        v_val_1079_,
                        v_x_1056_,
                        v_x_1057_,
                    );
                    v___x_1085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1085_, 0, v___x_1084_);
                    v___y_1073_ = v___x_1085_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1079_);
                    leanh::lean_dec(v_key_1078_);
                    if v_isShared_1082_ == 0 {
                        leanh::lean_ctor_set(v___x_1081_, 1, v_x_1057_);
                        leanh::lean_ctor_set(v___x_1081_, 0, v_x_1056_);
                        v___x_1087_ = v___x_1081_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1088_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_x_1056_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_x_1057_);
                        v___x_1087_ = v_reuseFailAlloc_1088_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1073_ = v___x_1087_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1094_ = lean_usize_shift_right(v_x_1054_, v___x_1059_);
                v___x_1095_ = lean_usize_add(v_x_1055_, v___x_1060_);
                v___x_1096_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_node_1090_, v___x_1094_, v___x_1095_, v_x_1056_, v_x_1057_);
                if v_isShared_1093_ == 0 {
                    leanh::lean_ctor_set(v___x_1092_, 0, v___x_1096_);
                    v___x_1098_ = v___x_1092_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1099_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
                    v___x_1098_ = v_reuseFailAlloc_1099_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1073_ = v___x_1098_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1108_ == 0 {
                    v___x_1110_ = v___x_1107_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_ks_1104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_vs_1105_);
                    v___x_1110_ = v_reuseFailAlloc_1124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1111_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v___x_1110_, v_x_1056_, v_x_1057_);
                v___x_1119_ = 7usize;
                v___x_1120_ = lean_usize_dec_le(v___x_1119_, v_x_1055_);
                if v___x_1120_ == 0 {
                    v___x_1121_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1111_);
                    v___x_1122_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1123_ = lean_nat_dec_lt(v___x_1121_, v___x_1122_);
                    leanh::lean_dec(v___x_1121_);
                    v___y_1113_ = v___x_1123_;
                    state = 10;
                    continue;
                } else {
                    v___y_1113_ = v___x_1120_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1113_ == 0 {
                    v_ks_1114_ = leanh::lean_ctor_get(v_newNode_1111_, 0);
                    leanh::lean_inc_ref(v_ks_1114_);
                    v_vs_1115_ = leanh::lean_ctor_get(v_newNode_1111_, 1);
                    leanh::lean_inc_ref(v_vs_1115_);
                    leanh::lean_dec_ref(v_newNode_1111_);
                    v___x_1116_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2);
                    v___x_1118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_x_1055_, v_ks_1114_, v_vs_1115_, v___x_1116_, v___x_1117_);
                    leanh::lean_dec_ref(v_vs_1115_);
                    leanh::lean_dec_ref(v_ks_1114_);
                    return v___x_1118_;
                } else {
                    return v_newNode_1111_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(
    mut v_depth_1126_: usize,
    mut v_keys_1127_: *mut leanh::LeanObject,
    mut v_vals_1128_: *mut leanh::LeanObject,
    mut v_i_1129_: *mut leanh::LeanObject,
    mut v_entries_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: u8 = 0;
    let mut v_k_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: u64 = 0;
    let mut v_h_1136_: usize = 0;
    let mut v___x_1137_: usize = 0;
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: usize = 0;
    let mut v___x_1140_: usize = 0;
    let mut v___x_1141_: usize = 0;
    let mut v_h_1142_: usize = 0;
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1131_ = lean_array_get_size(v_keys_1127_);
                v___x_1132_ = lean_nat_dec_lt(v_i_1129_, v___x_1131_);
                if v___x_1132_ == 0 {
                    leanh::lean_dec(v_i_1129_);
                    return v_entries_1130_;
                } else {
                    v_k_1133_ = lean_array_fget_borrowed(v_keys_1127_, v_i_1129_);
                    v_v_1134_ = lean_array_fget_borrowed(v_vals_1128_, v_i_1129_);
                    v___x_1135_ = l_Lean_instHashableLevelMVarId_hash(v_k_1133_);
                    v_h_1136_ = lean_uint64_to_usize(v___x_1135_);
                    v___x_1137_ = 5usize;
                    v___x_1138_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1139_ = 1usize;
                    v___x_1140_ = lean_usize_sub(v_depth_1126_, v___x_1139_);
                    v___x_1141_ = lean_usize_mul(v___x_1137_, v___x_1140_);
                    v_h_1142_ = lean_usize_shift_right(v_h_1136_, v___x_1141_);
                    v___x_1143_ = lean_nat_add(v_i_1129_, v___x_1138_);
                    leanh::lean_dec(v_i_1129_);
                    leanh::lean_inc(v_v_1134_);
                    leanh::lean_inc(v_k_1133_);
                    v___x_1144_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_entries_1130_, v_h_1142_, v_depth_1126_, v_k_1133_, v_v_1134_);
                    v_i_1129_ = v___x_1143_;
                    v_entries_1130_ = v___x_1144_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg___boxed(
    mut v_depth_1146_: *mut leanh::LeanObject,
    mut v_keys_1147_: *mut leanh::LeanObject,
    mut v_vals_1148_: *mut leanh::LeanObject,
    mut v_i_1149_: *mut leanh::LeanObject,
    mut v_entries_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1151_: usize = 0;
    let mut v_res_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1151_ = leanh::lean_unbox_usize(v_depth_1146_);
    leanh::lean_dec(v_depth_1146_);
    v_res_1152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_boxed_1151_, v_keys_1147_, v_vals_1148_, v_i_1149_, v_entries_1150_);
    leanh::lean_dec_ref(v_vals_1148_);
    leanh::lean_dec_ref(v_keys_1147_);
    return v_res_1152_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_x_1153_: *mut leanh::LeanObject,
    mut v_x_1154_: *mut leanh::LeanObject,
    mut v_x_1155_: *mut leanh::LeanObject,
    mut v_x_1156_: *mut leanh::LeanObject,
    mut v_x_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_8941__boxed_1158_: usize = 0;
    let mut v_x_8942__boxed_1159_: usize = 0;
    let mut v_res_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_8941__boxed_1158_ = leanh::lean_unbox_usize(v_x_1154_);
    leanh::lean_dec(v_x_1154_);
    v_x_8942__boxed_1159_ = leanh::lean_unbox_usize(v_x_1155_);
    leanh::lean_dec(v_x_1155_);
    v_res_1160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_1153_, v_x_8941__boxed_1158_, v_x_8942__boxed_1159_, v_x_1156_, v_x_1157_);
    return v_res_1160_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(
    mut v_x_1161_: *mut leanh::LeanObject,
    mut v_x_1162_: *mut leanh::LeanObject,
    mut v_x_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1164_: u64 = 0;
    let mut v___x_1165_: usize = 0;
    let mut v___x_1166_: usize = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1164_ = l_Lean_instHashableLevelMVarId_hash(v_x_1162_);
    v___x_1165_ = lean_uint64_to_usize(v___x_1164_);
    v___x_1166_ = 1usize;
    v___x_1167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_1161_, v___x_1165_, v___x_1166_, v_x_1162_, v_x_1163_);
    return v___x_1167_;
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(
    mut v_mvarId_1168_: *mut leanh::LeanObject,
    mut v_val_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1180_: u8 = 0;
    let mut v_depth_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1204_: u8 = 0;
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1172_ = lean_st_ref_take(v___y_1170_);
                v_mctx_1173_ = leanh::lean_ctor_get(v___x_1172_, 0);
                v_cache_1174_ = leanh::lean_ctor_get(v___x_1172_, 1);
                v_zetaDeltaFVarIds_1175_ = leanh::lean_ctor_get(v___x_1172_, 2);
                v_postponed_1176_ = leanh::lean_ctor_get(v___x_1172_, 3);
                v_diag_1177_ = leanh::lean_ctor_get(v___x_1172_, 4);
                v_isSharedCheck_1205_ = (!leanh::lean_is_exclusive(v___x_1172_)) as u8;
                if v_isSharedCheck_1205_ == 0 {
                    v___x_1179_ = v___x_1172_;
                    v_isShared_1180_ = v_isSharedCheck_1205_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1177_);
                    leanh::lean_inc(v_postponed_1176_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1175_);
                    leanh::lean_inc(v_cache_1174_);
                    leanh::lean_inc(v_mctx_1173_);
                    leanh::lean_dec(v___x_1172_);
                    v___x_1179_ = leanh::lean_box(0);
                    v_isShared_1180_ = v_isSharedCheck_1205_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1181_ = leanh::lean_ctor_get(v_mctx_1173_, 0);
                v_levelAssignDepth_1182_ = leanh::lean_ctor_get(v_mctx_1173_, 1);
                v_lmvarCounter_1183_ = leanh::lean_ctor_get(v_mctx_1173_, 2);
                v_mvarCounter_1184_ = leanh::lean_ctor_get(v_mctx_1173_, 3);
                v_lDecls_1185_ = leanh::lean_ctor_get(v_mctx_1173_, 4);
                v_decls_1186_ = leanh::lean_ctor_get(v_mctx_1173_, 5);
                v_userNames_1187_ = leanh::lean_ctor_get(v_mctx_1173_, 6);
                v_lAssignment_1188_ = leanh::lean_ctor_get(v_mctx_1173_, 7);
                v_eAssignment_1189_ = leanh::lean_ctor_get(v_mctx_1173_, 8);
                v_dAssignment_1190_ = leanh::lean_ctor_get(v_mctx_1173_, 9);
                v_isSharedCheck_1204_ = (!leanh::lean_is_exclusive(v_mctx_1173_)) as u8;
                if v_isSharedCheck_1204_ == 0 {
                    v___x_1192_ = v_mctx_1173_;
                    v_isShared_1193_ = v_isSharedCheck_1204_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1190_);
                    leanh::lean_inc(v_eAssignment_1189_);
                    leanh::lean_inc(v_lAssignment_1188_);
                    leanh::lean_inc(v_userNames_1187_);
                    leanh::lean_inc(v_decls_1186_);
                    leanh::lean_inc(v_lDecls_1185_);
                    leanh::lean_inc(v_mvarCounter_1184_);
                    leanh::lean_inc(v_lmvarCounter_1183_);
                    leanh::lean_inc(v_levelAssignDepth_1182_);
                    leanh::lean_inc(v_depth_1181_);
                    leanh::lean_dec(v_mctx_1173_);
                    v___x_1192_ = leanh::lean_box(0);
                    v_isShared_1193_ = v_isSharedCheck_1204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1194_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_lAssignment_1188_, v_mvarId_1168_, v_val_1169_);
                if v_isShared_1193_ == 0 {
                    leanh::lean_ctor_set(v___x_1192_, 7, v___x_1194_);
                    v___x_1196_ = v___x_1192_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1203_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_depth_1181_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1203_,
                        1,
                        v_levelAssignDepth_1182_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_lmvarCounter_1183_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_mvarCounter_1184_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_lDecls_1185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 5, v_decls_1186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 6, v_userNames_1187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 7, v___x_1194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 8, v_eAssignment_1189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 9, v_dAssignment_1190_);
                    v___x_1196_ = v_reuseFailAlloc_1203_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1180_ == 0 {
                    leanh::lean_ctor_set(v___x_1179_, 0, v___x_1196_);
                    v___x_1198_ = v___x_1179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_cache_1174_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1202_,
                        2,
                        v_zetaDeltaFVarIds_1175_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_postponed_1176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_diag_1177_);
                    v___x_1198_ = v_reuseFailAlloc_1202_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1199_ = lean_st_ref_set(v___y_1170_, v___x_1198_);
                v___x_1200_ = leanh::lean_box(0);
                v___x_1201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1201_, 0, v___x_1200_);
                return v___x_1201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg___boxed(
    mut v_mvarId_1206_: *mut leanh::LeanObject,
    mut v_val_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
    mut v___y_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1210_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_1206_, v_val_1207_, v___y_1208_);
    leanh::lean_dec(v___y_1208_);
    return v_res_1210_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_keys_1211_: *mut leanh::LeanObject,
    mut v_vals_1212_: *mut leanh::LeanObject,
    mut v_i_1213_: *mut leanh::LeanObject,
    mut v_k_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1215_ = lean_array_get_size(v_keys_1211_);
                v___x_1216_ = lean_nat_dec_lt(v_i_1213_, v___x_1215_);
                if v___x_1216_ == 0 {
                    leanh::lean_dec(v_i_1213_);
                    v___x_1217_ = leanh::lean_box(0);
                    return v___x_1217_;
                } else {
                    v_k_x27_1218_ = lean_array_fget_borrowed(v_keys_1211_, v_i_1213_);
                    v___x_1219_ = l_Lean_instBEqLevelMVarId_beq(v_k_1214_, v_k_x27_1218_);
                    if v___x_1219_ == 0 {
                        v___x_1220_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1221_ = lean_nat_add(v_i_1213_, v___x_1220_);
                        leanh::lean_dec(v_i_1213_);
                        v_i_1213_ = v___x_1221_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1223_ = lean_array_fget_borrowed(v_vals_1212_, v_i_1213_);
                        leanh::lean_dec(v_i_1213_);
                        leanh::lean_inc(v___x_1223_);
                        v___x_1224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1224_, 0, v___x_1223_);
                        return v___x_1224_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_1225_: *mut leanh::LeanObject,
    mut v_vals_1226_: *mut leanh::LeanObject,
    mut v_i_1227_: *mut leanh::LeanObject,
    mut v_k_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_1225_, v_vals_1226_, v_i_1227_, v_k_1228_);
    leanh::lean_dec(v_k_1228_);
    leanh::lean_dec_ref(v_vals_1226_);
    leanh::lean_dec_ref(v_keys_1225_);
    return v_res_1229_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(
    mut v_x_1230_: *mut leanh::LeanObject,
    mut v_x_1231_: usize,
    mut v_x_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: usize = 0;
    let mut v___x_1236_: usize = 0;
    let mut v___x_1237_: usize = 0;
    let mut v_j_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: u8 = 0;
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: usize = 0;
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1230_) == 0 {
                    v_es_1233_ = leanh::lean_ctor_get(v_x_1230_, 0);
                    v___x_1234_ = leanh::lean_box(2);
                    v___x_1235_ = 5usize;
                    v___x_1236_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1);
                    v___x_1237_ = lean_usize_land(v_x_1231_, v___x_1236_);
                    v_j_1238_ = lean_usize_to_nat(v___x_1237_);
                    v___x_1239_ = lean_array_get_borrowed(v___x_1234_, v_es_1233_, v_j_1238_);
                    leanh::lean_dec(v_j_1238_);
                    match leanh::lean_obj_tag(v___x_1239_) {
                        0 => {
                            v_key_1240_ = leanh::lean_ctor_get(v___x_1239_, 0);
                            v_val_1241_ = leanh::lean_ctor_get(v___x_1239_, 1);
                            v___x_1242_ = l_Lean_instBEqLevelMVarId_beq(v_x_1232_, v_key_1240_);
                            if v___x_1242_ == 0 {
                                v___x_1243_ = leanh::lean_box(0);
                                return v___x_1243_;
                            } else {
                                leanh::lean_inc(v_val_1241_);
                                v___x_1244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1244_, 0, v_val_1241_);
                                return v___x_1244_;
                            }
                        }
                        1 => {
                            v_node_1245_ = leanh::lean_ctor_get(v___x_1239_, 0);
                            v___x_1246_ = lean_usize_shift_right(v_x_1231_, v___x_1235_);
                            v_x_1230_ = v_node_1245_;
                            v_x_1231_ = v___x_1246_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1248_ = leanh::lean_box(0);
                            return v___x_1248_;
                        }
                    }
                } else {
                    v_ks_1249_ = leanh::lean_ctor_get(v_x_1230_, 0);
                    v_vs_1250_ = leanh::lean_ctor_get(v_x_1230_, 1);
                    v___x_1251_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1252_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_ks_1249_, v_vs_1250_, v___x_1251_, v_x_1232_);
                    return v___x_1252_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_1253_: *mut leanh::LeanObject,
    mut v_x_1254_: *mut leanh::LeanObject,
    mut v_x_1255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_9185__boxed_1256_: usize = 0;
    let mut v_res_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_9185__boxed_1256_ = leanh::lean_unbox_usize(v_x_1254_);
    leanh::lean_dec(v_x_1254_);
    v_res_1257_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_1253_, v_x_9185__boxed_1256_, v_x_1255_);
    leanh::lean_dec(v_x_1255_);
    leanh::lean_dec_ref(v_x_1253_);
    return v_res_1257_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(
    mut v_x_1258_: *mut leanh::LeanObject,
    mut v_x_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1260_: u64 = 0;
    let mut v___x_1261_: usize = 0;
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ = l_Lean_instHashableLevelMVarId_hash(v_x_1259_);
    v___x_1261_ = lean_uint64_to_usize(v___x_1260_);
    v___x_1262_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_1258_, v___x_1261_, v_x_1259_);
    return v___x_1262_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg___boxed(
    mut v_x_1263_: *mut leanh::LeanObject,
    mut v_x_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_1263_, v_x_1264_);
    leanh::lean_dec(v_x_1264_);
    leanh::lean_dec_ref(v_x_1263_);
    return v_res_1265_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3;
    v___x_1277_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5;
    v___x_1278_ = l_Lean_Name_append(v___x_1277_, v___x_1276_);
    return v___x_1278_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7;
    v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
    return v___x_1281_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9;
    v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
    return v___x_1284_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13;
    v___x_1289_ = leanh::lean_unsigned_to_nat(24);
    v___x_1290_ = leanh::lean_unsigned_to_nat(55);
    v___x_1291_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12;
    v___x_1292_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11;
    v___x_1293_ = l_mkPanicMessageWithDecl(
        v___x_1292_,
        v___x_1291_,
        v___x_1290_,
        v___x_1289_,
        v___x_1288_,
    );
    return v___x_1293_;
}
pub unsafe fn l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(
    mut v_x_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: u8,
    mut v_a_1296_: *mut leanh::LeanObject,
    mut v_a_1297_: *mut leanh::LeanObject,
    mut v_a_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v_val_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1331_: u8 = 0;
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1346_: u8 = 0;
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1354_: u8 = 0;
    let mut v___y_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_unused_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut v_options_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1379_: u8 = 0;
    let mut v_inheritedTraceOptions_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v_a_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1409_: u8 = 0;
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut v_a_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v_val_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1294_) {
                0 => {
                    v___x_1333_ = leanh::lean_box(0);
                    v___x_1334_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1334_, 0, v___x_1333_);
                    return v___x_1334_;
                }
                4 => {
                    leanh::lean_dec_ref_known(v_x_1294_, 1);
                    v___x_1335_ = leanh::lean_box(0);
                    v___x_1336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1336_, 0, v___x_1335_);
                    return v___x_1336_;
                }
                5 => {
                    v_a_1337_ = leanh::lean_ctor_get(v_x_1294_, 0);
                    leanh::lean_inc(v_a_1337_);
                    leanh::lean_dec_ref_known(v_x_1294_, 1);
                    v___x_1338_ = lean_st_ref_get(v_a_1297_);
                    v_mctx_1339_ = leanh::lean_ctor_get(v___x_1338_, 0);
                    leanh::lean_inc_ref(v_mctx_1339_);
                    leanh::lean_dec(v___x_1338_);
                    v_lAssignment_1340_ = leanh::lean_ctor_get(v_mctx_1339_, 7);
                    leanh::lean_inc_ref(v_lAssignment_1340_);
                    leanh::lean_dec_ref(v_mctx_1339_);
                    v___x_1341_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_lAssignment_1340_, v_a_1337_);
                    leanh::lean_dec_ref(v_lAssignment_1340_);
                    if leanh::lean_obj_tag(v___x_1341_) == 0 {
                        leanh::lean_inc(v_a_1337_);
                        v___x_1342_ = l_Lean_LMVarId_isReadOnly(
                            v_a_1337_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_,
                        );
                        if leanh::lean_obj_tag(v___x_1342_) == 0 {
                            v_a_1343_ = leanh::lean_ctor_get(v___x_1342_, 0);
                            v_isSharedCheck_1413_ =
                                (!leanh::lean_is_exclusive(v___x_1342_)) as u8;
                            if v_isSharedCheck_1413_ == 0 {
                                v___x_1345_ = v___x_1342_;
                                v_isShared_1346_ = v_isSharedCheck_1413_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1343_);
                                leanh::lean_dec(v___x_1342_);
                                v___x_1345_ = leanh::lean_box(0);
                                v_isShared_1346_ = v_isSharedCheck_1413_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1337_);
                            v_a_1414_ = leanh::lean_ctor_get(v___x_1342_, 0);
                            v_isSharedCheck_1421_ =
                                (!leanh::lean_is_exclusive(v___x_1342_)) as u8;
                            if v_isSharedCheck_1421_ == 0 {
                                v___x_1416_ = v___x_1342_;
                                v_isShared_1417_ = v_isSharedCheck_1421_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1414_);
                                leanh::lean_dec(v___x_1342_);
                                v___x_1416_ = leanh::lean_box(0);
                                v_isShared_1417_ = v_isSharedCheck_1421_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1337_);
                        v_val_1422_ = leanh::lean_ctor_get(v___x_1341_, 0);
                        leanh::lean_inc(v_val_1422_);
                        leanh::lean_dec_ref_known(v___x_1341_, 1);
                        v_x_1294_ = v_val_1422_;
                        state = 0;
                        continue;
                    }
                }
                1 => {
                    v_a_1424_ = leanh::lean_ctor_get(v_x_1294_, 0);
                    leanh::lean_inc(v_a_1424_);
                    leanh::lean_dec_ref_known(v_x_1294_, 1);
                    v___x_1425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1425_, 0, v_a_1424_);
                    v___x_1426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1426_, 0, v___x_1425_);
                    return v___x_1426_;
                }
                _ => match leanh::lean_obj_tag(v_x_1294_) {
                    2 => {
                        v_a_1427_ = leanh::lean_ctor_get(v_x_1294_, 0);
                        leanh::lean_inc(v_a_1427_);
                        v_a_1428_ = leanh::lean_ctor_get(v_x_1294_, 1);
                        leanh::lean_inc(v_a_1428_);
                        leanh::lean_dec_ref_known(v_x_1294_, 2);
                        v_u_1305_ = v_a_1427_;
                        v_v_1306_ = v_a_1428_;
                        v___y_1307_ = v_a_1296_;
                        v___y_1308_ = v_a_1297_;
                        v___y_1309_ = v_a_1298_;
                        v___y_1310_ = v_a_1299_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_a_1429_ = leanh::lean_ctor_get(v_x_1294_, 0);
                        leanh::lean_inc(v_a_1429_);
                        v_a_1430_ = leanh::lean_ctor_get(v_x_1294_, 1);
                        leanh::lean_inc(v_a_1430_);
                        leanh::lean_dec_ref_known(v_x_1294_, 2);
                        v_u_1305_ = v_a_1429_;
                        v_v_1306_ = v_a_1430_;
                        v___y_1307_ = v_a_1296_;
                        v___y_1308_ = v_a_1297_;
                        v___y_1309_ = v_a_1298_;
                        v___y_1310_ = v_a_1299_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec(v_x_1294_);
                        v___x_1431_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14);
                        v___x_1432_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v___x_1431_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
                        return v___x_1432_;
                    }
                },
            },
            1 => {
                v___x_1302_ = leanh::lean_box(0);
                v___x_1303_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1303_, 0, v___x_1302_);
                return v___x_1303_;
            }
            2 => {
                v___x_1311_ = 0;
                v___x_1312_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(
                    v_u_1305_,
                    v___x_1311_,
                    v___y_1307_,
                    v___y_1308_,
                    v___y_1309_,
                    v___y_1310_,
                );
                if leanh::lean_obj_tag(v___x_1312_) == 0 {
                    v_a_1313_ = leanh::lean_ctor_get(v___x_1312_, 0);
                    leanh::lean_inc(v_a_1313_);
                    leanh::lean_dec_ref_known(v___x_1312_, 1);
                    if leanh::lean_obj_tag(v_a_1313_) == 0 {
                        leanh::lean_dec(v_v_1306_);
                        state = 1;
                        continue;
                    } else {
                        v_val_1314_ = leanh::lean_ctor_get(v_a_1313_, 0);
                        leanh::lean_inc(v_val_1314_);
                        leanh::lean_dec_ref_known(v_a_1313_, 1);
                        v___x_1315_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(
                            v_v_1306_,
                            v___x_1311_,
                            v___y_1307_,
                            v___y_1308_,
                            v___y_1309_,
                            v___y_1310_,
                        );
                        if leanh::lean_obj_tag(v___x_1315_) == 0 {
                            v_a_1316_ = leanh::lean_ctor_get(v___x_1315_, 0);
                            v_isSharedCheck_1332_ =
                                (!leanh::lean_is_exclusive(v___x_1315_)) as u8;
                            if v_isSharedCheck_1332_ == 0 {
                                v___x_1318_ = v___x_1315_;
                                v_isShared_1319_ = v_isSharedCheck_1332_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1316_);
                                leanh::lean_dec(v___x_1315_);
                                v___x_1318_ = leanh::lean_box(0);
                                v_isShared_1319_ = v_isSharedCheck_1332_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_1314_);
                            return v___x_1315_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_v_1306_);
                    return v___x_1312_;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_1316_) == 0 {
                    leanh::lean_del_object(v___x_1318_);
                    leanh::lean_dec(v_val_1314_);
                    state = 1;
                    continue;
                } else {
                    v_val_1320_ = leanh::lean_ctor_get(v_a_1316_, 0);
                    v_isSharedCheck_1331_ = (!leanh::lean_is_exclusive(v_a_1316_)) as u8;
                    if v_isSharedCheck_1331_ == 0 {
                        v___x_1322_ = v_a_1316_;
                        v_isShared_1323_ = v_isSharedCheck_1331_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1320_);
                        leanh::lean_dec(v_a_1316_);
                        v___x_1322_ = leanh::lean_box(0);
                        v_isShared_1323_ = v_isSharedCheck_1331_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1324_ = l_Lean_mkLevelMax_x27(v_val_1314_, v_val_1320_);
                if v_isShared_1323_ == 0 {
                    leanh::lean_ctor_set(v___x_1322_, 0, v___x_1324_);
                    v___x_1326_ = v___x_1322_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1330_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1324_);
                    v___x_1326_ = v_reuseFailAlloc_1330_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1319_ == 0 {
                    leanh::lean_ctor_set(v___x_1318_, 0, v___x_1326_);
                    v___x_1328_ = v___x_1318_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1329_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
                    v___x_1328_ = v_reuseFailAlloc_1329_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1328_;
            }
            7 => {
                v___x_1347_ = (leanh::lean_unbox(v_a_1343_) as u8);
                leanh::lean_dec(v_a_1343_);
                if v___x_1347_ == 0 {
                    if v_a_1295_ == 0 {
                        leanh::lean_dec(v_a_1337_);
                        if v_isShared_1346_ == 0 {
                            leanh::lean_ctor_set(v___x_1345_, 0, v___x_1341_);
                            v___x_1349_ = v___x_1345_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_1350_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1341_);
                            v___x_1349_ = v_reuseFailAlloc_1350_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1345_);
                        v___x_1351_ = l_Lean_Meta_mkFreshLevelMVar(
                            v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_,
                        );
                        if leanh::lean_obj_tag(v___x_1351_) == 0 {
                            v_a_1352_ = leanh::lean_ctor_get(v___x_1351_, 0);
                            leanh::lean_inc(v_a_1352_);
                            leanh::lean_dec_ref_known(v___x_1351_, 1);
                            v_options_1378_ = leanh::lean_ctor_get(v_a_1298_, 2);
                            v_hasTrace_1379_ = leanh::lean_ctor_get_uint8(
                                v_options_1378_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_1379_ == 0 {
                                v___y_1354_ = v_a_1295_;
                                v___y_1355_ = v_a_1296_;
                                v___y_1356_ = v_a_1297_;
                                v___y_1357_ = v_a_1298_;
                                v___y_1358_ = v_a_1299_;
                                state = 9;
                                continue;
                            } else {
                                v_inheritedTraceOptions_1380_ =
                                    leanh::lean_ctor_get(v_a_1298_, 13);
                                v___x_1381_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3;
                                v___x_1382_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6);
                                v___x_1383_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_1380_,
                                        v_options_1378_,
                                        v___x_1382_,
                                    );
                                if v___x_1383_ == 0 {
                                    v___y_1354_ = v_a_1295_;
                                    v___y_1355_ = v_a_1296_;
                                    v___y_1356_ = v_a_1297_;
                                    v___y_1357_ = v_a_1298_;
                                    v___y_1358_ = v_a_1299_;
                                    state = 9;
                                    continue;
                                } else {
                                    v___x_1384_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8);
                                    leanh::lean_inc(v_a_1337_);
                                    v___x_1385_ = l_Lean_mkLevelMVar(v_a_1337_);
                                    v___x_1386_ = l_Lean_MessageData_ofLevel(v___x_1385_);
                                    v___x_1387_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1387_, 0, v___x_1384_);
                                    leanh::lean_ctor_set(v___x_1387_, 1, v___x_1386_);
                                    v___x_1388_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10);
                                    v___x_1389_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1389_, 0, v___x_1387_);
                                    leanh::lean_ctor_set(v___x_1389_, 1, v___x_1388_);
                                    leanh::lean_inc(v_a_1352_);
                                    v___x_1390_ = l_Lean_Level_succ___override(v_a_1352_);
                                    v___x_1391_ = l_Lean_MessageData_ofLevel(v___x_1390_);
                                    v___x_1392_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1392_, 0, v___x_1389_);
                                    leanh::lean_ctor_set(v___x_1392_, 1, v___x_1391_);
                                    v___x_1393_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v___x_1381_, v___x_1392_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
                                    if leanh::lean_obj_tag(v___x_1393_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_1393_, 1);
                                        v___y_1354_ = v_a_1295_;
                                        v___y_1355_ = v_a_1296_;
                                        v___y_1356_ = v_a_1297_;
                                        v___y_1357_ = v_a_1298_;
                                        v___y_1358_ = v_a_1299_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_1352_);
                                        leanh::lean_dec(v_a_1337_);
                                        v_a_1394_ = leanh::lean_ctor_get(v___x_1393_, 0);
                                        v_isSharedCheck_1401_ =
                                            (!leanh::lean_is_exclusive(v___x_1393_)) as u8;
                                        if v_isSharedCheck_1401_ == 0 {
                                            v___x_1396_ = v___x_1393_;
                                            v_isShared_1397_ = v_isSharedCheck_1401_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1394_);
                                            leanh::lean_dec(v___x_1393_);
                                            v___x_1396_ = leanh::lean_box(0);
                                            v_isShared_1397_ = v_isSharedCheck_1401_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1337_);
                            v_a_1402_ = leanh::lean_ctor_get(v___x_1351_, 0);
                            v_isSharedCheck_1409_ =
                                (!leanh::lean_is_exclusive(v___x_1351_)) as u8;
                            if v_isSharedCheck_1409_ == 0 {
                                v___x_1404_ = v___x_1351_;
                                v_isShared_1405_ = v_isSharedCheck_1409_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1402_);
                                leanh::lean_dec(v___x_1351_);
                                v___x_1404_ = leanh::lean_box(0);
                                v_isShared_1405_ = v_isSharedCheck_1409_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1337_);
                    if v_isShared_1346_ == 0 {
                        leanh::lean_ctor_set(v___x_1345_, 0, v___x_1341_);
                        v___x_1411_ = v___x_1345_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1341_);
                        v___x_1411_ = v_reuseFailAlloc_1412_;
                        state = 18;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_1349_;
            }
            9 => {
                leanh::lean_inc(v_a_1352_);
                v___x_1359_ = l_Lean_Level_succ___override(v_a_1352_);
                v___x_1360_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_a_1337_, v___x_1359_, v___y_1356_);
                if leanh::lean_obj_tag(v___x_1360_) == 0 {
                    v_isSharedCheck_1368_ = (!leanh::lean_is_exclusive(v___x_1360_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v_unused_1369_ = leanh::lean_ctor_get(v___x_1360_, 0);
                        leanh::lean_dec(v_unused_1369_);
                        v___x_1362_ = v___x_1360_;
                        v_isShared_1363_ = v_isSharedCheck_1368_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1360_);
                        v___x_1362_ = leanh::lean_box(0);
                        v_isShared_1363_ = v_isSharedCheck_1368_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1352_);
                    v_a_1370_ = leanh::lean_ctor_get(v___x_1360_, 0);
                    v_isSharedCheck_1377_ = (!leanh::lean_is_exclusive(v___x_1360_)) as u8;
                    if v_isSharedCheck_1377_ == 0 {
                        v___x_1372_ = v___x_1360_;
                        v_isShared_1373_ = v_isSharedCheck_1377_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1370_);
                        leanh::lean_dec(v___x_1360_);
                        v___x_1372_ = leanh::lean_box(0);
                        v_isShared_1373_ = v_isSharedCheck_1377_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                v___x_1364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1364_, 0, v_a_1352_);
                if v_isShared_1363_ == 0 {
                    leanh::lean_ctor_set(v___x_1362_, 0, v___x_1364_);
                    v___x_1366_ = v___x_1362_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
                    v___x_1366_ = v_reuseFailAlloc_1367_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1366_;
            }
            12 => {
                if v_isShared_1373_ == 0 {
                    v___x_1375_ = v___x_1372_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
                    v___x_1375_ = v_reuseFailAlloc_1376_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1375_;
            }
            14 => {
                if v_isShared_1397_ == 0 {
                    v___x_1399_ = v___x_1396_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
                    v___x_1399_ = v_reuseFailAlloc_1400_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1399_;
            }
            16 => {
                if v_isShared_1405_ == 0 {
                    v___x_1407_ = v___x_1404_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1408_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
                    v___x_1407_ = v_reuseFailAlloc_1408_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1407_;
            }
            18 => {
                return v___x_1411_;
            }
            19 => {
                if v_isShared_1417_ == 0 {
                    v___x_1419_ = v___x_1416_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
                    v___x_1419_ = v_reuseFailAlloc_1420_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___boxed(
    mut v_x_1433_: *mut leanh::LeanObject,
    mut v_a_1434_: *mut leanh::LeanObject,
    mut v_a_1435_: *mut leanh::LeanObject,
    mut v_a_1436_: *mut leanh::LeanObject,
    mut v_a_1437_: *mut leanh::LeanObject,
    mut v_a_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1440_: u8 = 0;
    let mut v_res_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1440_ = (leanh::lean_unbox(v_a_1434_) as u8);
    v_res_1441_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(
        v_x_1433_,
        v_a_boxed_1440_,
        v_a_1435_,
        v_a_1436_,
        v_a_1437_,
        v_a_1438_,
    );
    leanh::lean_dec(v_a_1438_);
    leanh::lean_dec_ref(v_a_1437_);
    leanh::lean_dec(v_a_1436_);
    leanh::lean_dec_ref(v_a_1435_);
    return v_res_1441_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(
    mut v_00_u03b2_1442_: *mut leanh::LeanObject,
    mut v_x_1443_: *mut leanh::LeanObject,
    mut v_x_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_1443_, v_x_1444_);
    return v___x_1445_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___boxed(
    mut v_00_u03b2_1446_: *mut leanh::LeanObject,
    mut v_x_1447_: *mut leanh::LeanObject,
    mut v_x_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(v_00_u03b2_1446_, v_x_1447_, v_x_1448_);
    leanh::lean_dec(v_x_1448_);
    leanh::lean_dec_ref(v_x_1447_);
    return v_res_1449_;
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(
    mut v_mvarId_1450_: *mut leanh::LeanObject,
    mut v_val_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: u8,
    mut v___y_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
    mut v___y_1455_: *mut leanh::LeanObject,
    mut v___y_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1458_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_1450_, v_val_1451_, v___y_1454_);
    return v___x_1458_;
}
pub unsafe fn l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___boxed(
    mut v_mvarId_1459_: *mut leanh::LeanObject,
    mut v_val_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
    mut v___y_1465_: *mut leanh::LeanObject,
    mut v___y_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9598__boxed_1467_: u8 = 0;
    let mut v_res_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9598__boxed_1467_ = (leanh::lean_unbox(v___y_1461_) as u8);
    v_res_1468_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(v_mvarId_1459_, v_val_1460_, v___y_9598__boxed_1467_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
    leanh::lean_dec(v___y_1465_);
    leanh::lean_dec_ref(v___y_1464_);
    leanh::lean_dec(v___y_1463_);
    leanh::lean_dec_ref(v___y_1462_);
    return v_res_1468_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(
    mut v_cls_1469_: *mut leanh::LeanObject,
    mut v_msg_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: u8,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
    mut v___y_1474_: *mut leanh::LeanObject,
    mut v___y_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_1469_, v_msg_1470_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
    return v___x_1477_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___boxed(
    mut v_cls_1478_: *mut leanh::LeanObject,
    mut v_msg_1479_: *mut leanh::LeanObject,
    mut v___y_1480_: *mut leanh::LeanObject,
    mut v___y_1481_: *mut leanh::LeanObject,
    mut v___y_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v___y_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9618__boxed_1486_: u8 = 0;
    let mut v_res_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9618__boxed_1486_ = (leanh::lean_unbox(v___y_1480_) as u8);
    v_res_1487_ =
        l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(
            v_cls_1478_,
            v_msg_1479_,
            v___y_9618__boxed_1486_,
            v___y_1481_,
            v___y_1482_,
            v___y_1483_,
            v___y_1484_,
        );
    leanh::lean_dec(v___y_1484_);
    leanh::lean_dec_ref(v___y_1483_);
    leanh::lean_dec(v___y_1482_);
    leanh::lean_dec_ref(v___y_1481_);
    return v_res_1487_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(
    mut v_00_u03b2_1488_: *mut leanh::LeanObject,
    mut v_x_1489_: *mut leanh::LeanObject,
    mut v_x_1490_: usize,
    mut v_x_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_1489_, v_x_1490_, v_x_1491_);
    return v___x_1492_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1493_: *mut leanh::LeanObject,
    mut v_x_1494_: *mut leanh::LeanObject,
    mut v_x_1495_: *mut leanh::LeanObject,
    mut v_x_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_9639__boxed_1497_: usize = 0;
    let mut v_res_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_9639__boxed_1497_ = leanh::lean_unbox_usize(v_x_1495_);
    leanh::lean_dec(v_x_1495_);
    v_res_1498_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(v_00_u03b2_1493_, v_x_1494_, v_x_9639__boxed_1497_, v_x_1496_);
    leanh::lean_dec(v_x_1496_);
    leanh::lean_dec_ref(v_x_1494_);
    return v_res_1498_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2(
    mut v_00_u03b2_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
    mut v_x_1501_: *mut leanh::LeanObject,
    mut v_x_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_x_1500_, v_x_1501_, v_x_1502_);
    return v___x_1503_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1504_: *mut leanh::LeanObject,
    mut v_keys_1505_: *mut leanh::LeanObject,
    mut v_vals_1506_: *mut leanh::LeanObject,
    mut v_heq_1507_: *mut leanh::LeanObject,
    mut v_i_1508_: *mut leanh::LeanObject,
    mut v_k_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_1505_, v_vals_1506_, v_i_1508_, v_k_1509_);
    return v___x_1510_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1511_: *mut leanh::LeanObject,
    mut v_keys_1512_: *mut leanh::LeanObject,
    mut v_vals_1513_: *mut leanh::LeanObject,
    mut v_heq_1514_: *mut leanh::LeanObject,
    mut v_i_1515_: *mut leanh::LeanObject,
    mut v_k_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(v_00_u03b2_1511_, v_keys_1512_, v_vals_1513_, v_heq_1514_, v_i_1515_, v_k_1516_);
    leanh::lean_dec(v_k_1516_);
    leanh::lean_dec_ref(v_vals_1513_);
    leanh::lean_dec_ref(v_keys_1512_);
    return v_res_1517_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1518_: *mut leanh::LeanObject,
    mut v_x_1519_: *mut leanh::LeanObject,
    mut v_x_1520_: usize,
    mut v_x_1521_: usize,
    mut v_x_1522_: *mut leanh::LeanObject,
    mut v_x_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_1519_, v_x_1520_, v_x_1521_, v_x_1522_, v_x_1523_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_1525_: *mut leanh::LeanObject,
    mut v_x_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_x_1528_: *mut leanh::LeanObject,
    mut v_x_1529_: *mut leanh::LeanObject,
    mut v_x_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_9660__boxed_1531_: usize = 0;
    let mut v_x_9661__boxed_1532_: usize = 0;
    let mut v_res_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_9660__boxed_1531_ = leanh::lean_unbox_usize(v_x_1527_);
    leanh::lean_dec(v_x_1527_);
    v_x_9661__boxed_1532_ = leanh::lean_unbox_usize(v_x_1528_);
    leanh::lean_dec(v_x_1528_);
    v_res_1533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1525_, v_x_1526_, v_x_9660__boxed_1531_, v_x_9661__boxed_1532_, v_x_1529_, v_x_1530_);
    return v_res_1533_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8(
    mut v_00_u03b2_1534_: *mut leanh::LeanObject,
    mut v_n_1535_: *mut leanh::LeanObject,
    mut v_k_1536_: *mut leanh::LeanObject,
    mut v_v_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v_n_1535_, v_k_1536_, v_v_1537_);
    return v___x_1538_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(
    mut v_00_u03b2_1539_: *mut leanh::LeanObject,
    mut v_depth_1540_: usize,
    mut v_keys_1541_: *mut leanh::LeanObject,
    mut v_vals_1542_: *mut leanh::LeanObject,
    mut v_heq_1543_: *mut leanh::LeanObject,
    mut v_i_1544_: *mut leanh::LeanObject,
    mut v_entries_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_1540_, v_keys_1541_, v_vals_1542_, v_i_1544_, v_entries_1545_);
    return v___x_1546_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___boxed(
    mut v_00_u03b2_1547_: *mut leanh::LeanObject,
    mut v_depth_1548_: *mut leanh::LeanObject,
    mut v_keys_1549_: *mut leanh::LeanObject,
    mut v_vals_1550_: *mut leanh::LeanObject,
    mut v_heq_1551_: *mut leanh::LeanObject,
    mut v_i_1552_: *mut leanh::LeanObject,
    mut v_entries_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1554_: usize = 0;
    let mut v_res_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1554_ = leanh::lean_unbox_usize(v_depth_1548_);
    leanh::lean_dec(v_depth_1548_);
    v_res_1555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(v_00_u03b2_1547_, v_depth_boxed_1554_, v_keys_1549_, v_vals_1550_, v_heq_1551_, v_i_1552_, v_entries_1553_);
    leanh::lean_dec_ref(v_vals_1550_);
    leanh::lean_dec_ref(v_keys_1549_);
    return v_res_1555_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9(
    mut v_00_u03b2_1556_: *mut leanh::LeanObject,
    mut v_x_1557_: *mut leanh::LeanObject,
    mut v_x_1558_: *mut leanh::LeanObject,
    mut v_x_1559_: *mut leanh::LeanObject,
    mut v_x_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1561_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_x_1557_, v_x_1558_, v_x_1559_, v_x_1560_);
    return v___x_1561_;
}
pub unsafe fn l_Lean_Meta_decLevel_x3f(
    mut v_u_1562_: *mut leanh::LeanObject,
    mut v_a_1563_: *mut leanh::LeanObject,
    mut v_a_1564_: *mut leanh::LeanObject,
    mut v_a_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_unused_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_unused_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1568_ = lean_st_ref_get(v_a_1564_);
                v___x_1569_ = 1;
                v___x_1570_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(
                    v_u_1562_,
                    v___x_1569_,
                    v_a_1563_,
                    v_a_1564_,
                    v_a_1565_,
                    v_a_1566_,
                );
                if leanh::lean_obj_tag(v___x_1570_) == 0 {
                    v_a_1571_ = leanh::lean_ctor_get(v___x_1570_, 0);
                    leanh::lean_inc(v_a_1571_);
                    if leanh::lean_obj_tag(v_a_1571_) == 0 {
                        v_isSharedCheck_1593_ =
                            (!leanh::lean_is_exclusive(v___x_1570_)) as u8;
                        if v_isSharedCheck_1593_ == 0 {
                            v_unused_1594_ = leanh::lean_ctor_get(v___x_1570_, 0);
                            leanh::lean_dec(v_unused_1594_);
                            v___x_1573_ = v___x_1570_;
                            v_isShared_1574_ = v_isSharedCheck_1593_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1570_);
                            v___x_1573_ = leanh::lean_box(0);
                            v_isShared_1574_ = v_isSharedCheck_1593_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_1571_, 1);
                        leanh::lean_dec(v___x_1568_);
                        return v___x_1570_;
                    }
                } else {
                    leanh::lean_dec(v___x_1568_);
                    return v___x_1570_;
                }
            }
            1 => {
                v___x_1575_ = lean_st_ref_take(v_a_1564_);
                v_mctx_1576_ = leanh::lean_ctor_get(v___x_1568_, 0);
                leanh::lean_inc_ref(v_mctx_1576_);
                leanh::lean_dec(v___x_1568_);
                v_cache_1577_ = leanh::lean_ctor_get(v___x_1575_, 1);
                v_zetaDeltaFVarIds_1578_ = leanh::lean_ctor_get(v___x_1575_, 2);
                v_postponed_1579_ = leanh::lean_ctor_get(v___x_1575_, 3);
                v_diag_1580_ = leanh::lean_ctor_get(v___x_1575_, 4);
                v_isSharedCheck_1591_ = (!leanh::lean_is_exclusive(v___x_1575_)) as u8;
                if v_isSharedCheck_1591_ == 0 {
                    v_unused_1592_ = leanh::lean_ctor_get(v___x_1575_, 0);
                    leanh::lean_dec(v_unused_1592_);
                    v___x_1582_ = v___x_1575_;
                    v_isShared_1583_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1580_);
                    leanh::lean_inc(v_postponed_1579_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1578_);
                    leanh::lean_inc(v_cache_1577_);
                    leanh::lean_dec(v___x_1575_);
                    v___x_1582_ = leanh::lean_box(0);
                    v_isShared_1583_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1583_ == 0 {
                    leanh::lean_ctor_set(v___x_1582_, 0, v_mctx_1576_);
                    v___x_1585_ = v___x_1582_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_mctx_1576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_cache_1577_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1590_,
                        2,
                        v_zetaDeltaFVarIds_1578_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_postponed_1579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_diag_1580_);
                    v___x_1585_ = v_reuseFailAlloc_1590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1586_ = lean_st_ref_set(v_a_1564_, v___x_1585_);
                if v_isShared_1574_ == 0 {
                    v___x_1588_ = v___x_1573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1571_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_decLevel_x3f___boxed(
    mut v_u_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
    mut v_a_1598_: *mut leanh::LeanObject,
    mut v_a_1599_: *mut leanh::LeanObject,
    mut v_a_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Lean_Meta_decLevel_x3f(v_u_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
    leanh::lean_dec(v_a_1599_);
    leanh::lean_dec_ref(v_a_1598_);
    leanh::lean_dec(v_a_1597_);
    leanh::lean_dec_ref(v_a_1596_);
    return v_res_1601_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(
    mut v_msg_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
    mut v___y_1605_: *mut leanh::LeanObject,
    mut v___y_1606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1608_ = leanh::lean_ctor_get(v___y_1605_, 5);
                v___x_1609_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
                v_a_1610_ = leanh::lean_ctor_get(v___x_1609_, 0);
                v_isSharedCheck_1618_ = (!leanh::lean_is_exclusive(v___x_1609_)) as u8;
                if v_isSharedCheck_1618_ == 0 {
                    v___x_1612_ = v___x_1609_;
                    v_isShared_1613_ = v_isSharedCheck_1618_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1610_);
                    leanh::lean_dec(v___x_1609_);
                    v___x_1612_ = leanh::lean_box(0);
                    v_isShared_1613_ = v_isSharedCheck_1618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1608_);
                v___x_1614_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1614_, 0, v_ref_1608_);
                leanh::lean_ctor_set(v___x_1614_, 1, v_a_1610_);
                if v_isShared_1613_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1612_, 1);
                    leanh::lean_ctor_set(v___x_1612_, 0, v___x_1614_);
                    v___x_1616_ = v___x_1612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
                    v___x_1616_ = v_reuseFailAlloc_1617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg___boxed(
    mut v_msg_1619_: *mut leanh::LeanObject,
    mut v___y_1620_: *mut leanh::LeanObject,
    mut v___y_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(
        v_msg_1619_,
        v___y_1620_,
        v___y_1621_,
        v___y_1622_,
        v___y_1623_,
    );
    leanh::lean_dec(v___y_1623_);
    leanh::lean_dec_ref(v___y_1622_);
    leanh::lean_dec(v___y_1621_);
    leanh::lean_dec_ref(v___y_1620_);
    return v_res_1625_;
}
pub unsafe fn _init_l_Lean_Meta_decLevel___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lean_Meta_decLevel___closed__0;
    v___x_1628_ = l_Lean_stringToMessageData(v___x_1627_);
    return v___x_1628_;
}
pub unsafe fn _init_l_Lean_Meta_decLevel___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1630_ = l_Lean_Meta_decLevel___closed__2;
    v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
    return v___x_1631_;
}
pub unsafe fn l_Lean_Meta_decLevel(
    mut v_u_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
    mut v_a_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v_a_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1657_: u8 = 0;
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_u_1632_);
                v___x_1638_ =
                    l_Lean_Meta_decLevel_x3f(v_u_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
                if leanh::lean_obj_tag(v___x_1638_) == 0 {
                    v_a_1639_ = leanh::lean_ctor_get(v___x_1638_, 0);
                    v_isSharedCheck_1653_ = (!leanh::lean_is_exclusive(v___x_1638_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1641_ = v___x_1638_;
                        v_isShared_1642_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1639_);
                        leanh::lean_dec(v___x_1638_);
                        v___x_1641_ = leanh::lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_u_1632_);
                    v_a_1654_ = leanh::lean_ctor_get(v___x_1638_, 0);
                    v_isSharedCheck_1661_ = (!leanh::lean_is_exclusive(v___x_1638_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1656_ = v___x_1638_;
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1654_);
                        leanh::lean_dec(v___x_1638_);
                        v___x_1656_ = leanh::lean_box(0);
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1639_) == 0 {
                    leanh::lean_del_object(v___x_1641_);
                    v___x_1643_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_decLevel___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_decLevel___closed__1_once),
                        _init_l_Lean_Meta_decLevel___closed__1,
                    );
                    v___x_1644_ = l_Lean_MessageData_ofLevel(v_u_1632_);
                    v___x_1645_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1645_, 0, v___x_1643_);
                    leanh::lean_ctor_set(v___x_1645_, 1, v___x_1644_);
                    v___x_1646_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_decLevel___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_decLevel___closed__3_once),
                        _init_l_Lean_Meta_decLevel___closed__3,
                    );
                    v___x_1647_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1647_, 0, v___x_1645_);
                    leanh::lean_ctor_set(v___x_1647_, 1, v___x_1646_);
                    v___x_1648_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(
                        v___x_1647_,
                        v_a_1633_,
                        v_a_1634_,
                        v_a_1635_,
                        v_a_1636_,
                    );
                    return v___x_1648_;
                } else {
                    leanh::lean_dec(v_u_1632_);
                    v_val_1649_ = leanh::lean_ctor_get(v_a_1639_, 0);
                    leanh::lean_inc(v_val_1649_);
                    leanh::lean_dec_ref_known(v_a_1639_, 1);
                    if v_isShared_1642_ == 0 {
                        leanh::lean_ctor_set(v___x_1641_, 0, v_val_1649_);
                        v___x_1651_ = v___x_1641_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_val_1649_);
                        v___x_1651_ = v_reuseFailAlloc_1652_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1651_;
            }
            3 => {
                if v_isShared_1657_ == 0 {
                    v___x_1659_ = v___x_1656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
                    v___x_1659_ = v_reuseFailAlloc_1660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_decLevel___boxed(
    mut v_u_1662_: *mut leanh::LeanObject,
    mut v_a_1663_: *mut leanh::LeanObject,
    mut v_a_1664_: *mut leanh::LeanObject,
    mut v_a_1665_: *mut leanh::LeanObject,
    mut v_a_1666_: *mut leanh::LeanObject,
    mut v_a_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Lean_Meta_decLevel(v_u_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
    leanh::lean_dec(v_a_1666_);
    leanh::lean_dec_ref(v_a_1665_);
    leanh::lean_dec(v_a_1664_);
    leanh::lean_dec_ref(v_a_1663_);
    return v_res_1668_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(
    mut v_00_u03b1_1669_: *mut leanh::LeanObject,
    mut v_msg_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(
        v_msg_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
        v___y_1674_,
    );
    return v___x_1676_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___boxed(
    mut v_00_u03b1_1677_: *mut leanh::LeanObject,
    mut v_msg_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
    mut v___y_1682_: *mut leanh::LeanObject,
    mut v___y_1683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(
        v_00_u03b1_1677_,
        v_msg_1678_,
        v___y_1679_,
        v___y_1680_,
        v___y_1681_,
        v___y_1682_,
    );
    leanh::lean_dec(v___y_1682_);
    leanh::lean_dec_ref(v___y_1681_);
    leanh::lean_dec(v___y_1680_);
    leanh::lean_dec_ref(v___y_1679_);
    return v_res_1684_;
}
pub unsafe fn l_Lean_Meta_getDecLevel(
    mut v_type_1685_: *mut leanh::LeanObject,
    mut v_a_1686_: *mut leanh::LeanObject,
    mut v_a_1687_: *mut leanh::LeanObject,
    mut v_a_1688_: *mut leanh::LeanObject,
    mut v_a_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lean_Meta_getLevel(v_type_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
    if leanh::lean_obj_tag(v___x_1691_) == 0 {
        let mut v_a_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1692_ = leanh::lean_ctor_get(v___x_1691_, 0);
        leanh::lean_inc(v_a_1692_);
        leanh::lean_dec_ref_known(v___x_1691_, 1);
        v___x_1693_ =
            l_Lean_Meta_normalizeLevel(v_a_1692_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
        if leanh::lean_obj_tag(v___x_1693_) == 0 {
            let mut v_a_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1694_ = leanh::lean_ctor_get(v___x_1693_, 0);
            leanh::lean_inc(v_a_1694_);
            leanh::lean_dec_ref_known(v___x_1693_, 1);
            v___x_1695_ =
                l_Lean_Meta_decLevel(v_a_1694_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
            return v___x_1695_;
        } else {
            return v___x_1693_;
        }
    } else {
        return v___x_1691_;
    }
}
pub unsafe fn l_Lean_Meta_getDecLevel___boxed(
    mut v_type_1696_: *mut leanh::LeanObject,
    mut v_a_1697_: *mut leanh::LeanObject,
    mut v_a_1698_: *mut leanh::LeanObject,
    mut v_a_1699_: *mut leanh::LeanObject,
    mut v_a_1700_: *mut leanh::LeanObject,
    mut v_a_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_Meta_getDecLevel(v_type_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
    leanh::lean_dec(v_a_1700_);
    leanh::lean_dec_ref(v_a_1699_);
    leanh::lean_dec(v_a_1698_);
    leanh::lean_dec_ref(v_a_1697_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_Meta_getDecLevel_x3f(
    mut v_type_1703_: *mut leanh::LeanObject,
    mut v_a_1704_: *mut leanh::LeanObject,
    mut v_a_1705_: *mut leanh::LeanObject,
    mut v_a_1706_: *mut leanh::LeanObject,
    mut v_a_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_a_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1725_: u8 = 0;
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1709_ =
                    l_Lean_Meta_getLevel(v_type_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
                if leanh::lean_obj_tag(v___x_1709_) == 0 {
                    v_a_1710_ = leanh::lean_ctor_get(v___x_1709_, 0);
                    leanh::lean_inc(v_a_1710_);
                    leanh::lean_dec_ref_known(v___x_1709_, 1);
                    v___x_1711_ = l_Lean_Meta_normalizeLevel(
                        v_a_1710_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_,
                    );
                    if leanh::lean_obj_tag(v___x_1711_) == 0 {
                        v_a_1712_ = leanh::lean_ctor_get(v___x_1711_, 0);
                        leanh::lean_inc(v_a_1712_);
                        leanh::lean_dec_ref_known(v___x_1711_, 1);
                        v___x_1713_ = l_Lean_Meta_decLevel_x3f(
                            v_a_1712_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_,
                        );
                        return v___x_1713_;
                    } else {
                        v_a_1714_ = leanh::lean_ctor_get(v___x_1711_, 0);
                        v_isSharedCheck_1721_ =
                            (!leanh::lean_is_exclusive(v___x_1711_)) as u8;
                        if v_isSharedCheck_1721_ == 0 {
                            v___x_1716_ = v___x_1711_;
                            v_isShared_1717_ = v_isSharedCheck_1721_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1714_);
                            leanh::lean_dec(v___x_1711_);
                            v___x_1716_ = leanh::lean_box(0);
                            v_isShared_1717_ = v_isSharedCheck_1721_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_1722_ = leanh::lean_ctor_get(v___x_1709_, 0);
                    v_isSharedCheck_1729_ = (!leanh::lean_is_exclusive(v___x_1709_)) as u8;
                    if v_isSharedCheck_1729_ == 0 {
                        v___x_1724_ = v___x_1709_;
                        v_isShared_1725_ = v_isSharedCheck_1729_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1722_);
                        leanh::lean_dec(v___x_1709_);
                        v___x_1724_ = leanh::lean_box(0);
                        v_isShared_1725_ = v_isSharedCheck_1729_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1717_ == 0 {
                    v___x_1719_ = v___x_1716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
                    v___x_1719_ = v_reuseFailAlloc_1720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1719_;
            }
            3 => {
                if v_isShared_1725_ == 0 {
                    v___x_1727_ = v___x_1724_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
                    v___x_1727_ = v_reuseFailAlloc_1728_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getDecLevel_x3f___boxed(
    mut v_type_1730_: *mut leanh::LeanObject,
    mut v_a_1731_: *mut leanh::LeanObject,
    mut v_a_1732_: *mut leanh::LeanObject,
    mut v_a_1733_: *mut leanh::LeanObject,
    mut v_a_1734_: *mut leanh::LeanObject,
    mut v_a_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ =
        l_Lean_Meta_getDecLevel_x3f(v_type_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
    leanh::lean_dec(v_a_1734_);
    leanh::lean_dec_ref(v_a_1733_);
    leanh::lean_dec(v_a_1732_);
    leanh::lean_dec_ref(v_a_1731_);
    return v_res_1736_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = leanh::lean_unsigned_to_nat(3263537904);
    v___x_1779_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_;
    v___x_1780_ = l_Lean_Name_num___override(v___x_1779_, v___x_1778_);
    return v___x_1780_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_;
    v___x_1783_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
    v___x_1784_ = l_Lean_Name_str___override(v___x_1783_, v___x_1782_);
    return v___x_1784_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_;
    v___x_1787_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
    v___x_1788_ = l_Lean_Name_str___override(v___x_1787_, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = leanh::lean_unsigned_to_nat(2);
    v___x_1790_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
    v___x_1791_ = l_Lean_Name_num___override(v___x_1790_, v___x_1789_);
    return v___x_1791_;
}
pub unsafe fn l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1793_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3;
    v___x_1794_ = 0;
    v___x_1795_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
    v___x_1796_ = l_Lean_registerTraceClass(v___x_1793_, v___x_1794_, v___x_1795_);
    return v___x_1796_;
}
pub unsafe fn l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2____boxed(
    mut v_a_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
    return v_res_1798_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_DecLevel(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_DecLevel(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_DecLevel(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_DecLevel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_DecLevel(builtin);
}