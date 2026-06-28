// Lean compiler output
// Module: Init.Data.ByteArray.Basic
// Imports: Init.Data.UInt.BasicAux Init.Data.Array.DecidableEq Init.Data.List.Attach Init.Data.Array.Bootstrap Init.Data.Array.Lemmas Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::DecidableEq::{
    initialize_Init_Data_Array_DecidableEq, runtime_initialize_Init_Data_Array_DecidableEq,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::UInt::BasicAux::{
    initialize_Init_Data_UInt_BasicAux, runtime_initialize_Init_Data_UInt_BasicAux,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_uint8_of_nat,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_box_uint64, lean_box_usize, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint8_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_ByteArray_instBEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ByteArray_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_ByteArray_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_ByteArray_instInhabited: *mut LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_instEmptyCollection: *mut LeanObject = core::ptr::null_mut();
pub static l_ByteArray_uget___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_ByteArray_uget___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__0_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_ByteArray_uget___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__1_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_ByteArray_uget___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__2_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_ByteArray_uget___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__3_value) as *mut LeanObject;
static l_ByteArray_uget___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_ByteArray_uget___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_ByteArray_uget___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_ByteArray_uget___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_ByteArray_uget___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_ByteArray_uget___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__5_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_ByteArray_uget___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__6_value) as *mut LeanObject;
static l_ByteArray_uget___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_ByteArray_uget___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_ByteArray_uget___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_ByteArray_uget___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_ByteArray_uget___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_ByteArray_uget___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__8_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_ByteArray_uget___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__9_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__10_value: LeanStringObject<22> = LeanStringObject {
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
        116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105,
        99, 0,
    ],
};
static mut l_ByteArray_uget___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__10_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__10_value) as *mut LeanObject,
        3731765604234633101 as *mut LeanObject,
    ],
};
static mut l_ByteArray_uget___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__11_value) as *mut LeanObject;
pub static l_ByteArray_uget___auto__1___closed__12_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_ByteArray_uget___auto__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__12_value) as *mut LeanObject;
static mut l_ByteArray_uget___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_uget___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_uget___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_get___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_instGetElemNatUInt8LtSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value) as *mut LeanObject;
pub static mut l_ByteArray_instGetElemNatUInt8LtSize: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value) as *mut LeanObject;
pub static l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value)
        as *mut LeanObject;
pub static mut l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value)
        as *mut LeanObject;
pub static mut l_ByteArray_set___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_uset___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_ByteArray_instHashable___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ByteArray_instHashable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instHashable___closed__0_value) as *mut LeanObject;
pub static mut l_ByteArray_instHashable: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instHashable___closed__0_value) as *mut LeanObject;
pub static l_ByteArray_instAppend___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_fastAppend___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ByteArray_instAppend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instAppend___closed__0_value) as *mut LeanObject;
pub static mut l_ByteArray_instAppend: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instAppend___closed__0_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteArray_foldl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__0_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteArray_foldl___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__1_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteArray_foldl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__2_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteArray_foldl___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__3_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteArray_foldl___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__4_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteArray_foldl___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__5_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteArray_foldl___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__6_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_ByteArray_foldl___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__7_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_ByteArray_foldl___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__8_value) as *mut LeanObject;
pub static l_ByteArray_foldl___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_ByteArray_foldl___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__9_value) as *mut LeanObject;
static mut l_ByteArray_instInhabitedIterator_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_instInhabitedIterator_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_ByteArray_instInhabitedIterator_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_instInhabitedIterator: *mut LeanObject = core::ptr::null_mut();
pub static l_ByteArray_instSizeOfIterator___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_ByteArray_instSizeOfIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_instSizeOfIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instSizeOfIterator___closed__0_value) as *mut LeanObject;
pub static mut l_ByteArray_instSizeOfIterator: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_instSizeOfIterator___closed__0_value) as *mut LeanObject;
static mut l_ByteArray_Iterator_curr___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_Iterator_curr___closed__0: u8 = 0;
pub unsafe fn l_ByteArray_beq___boxed(
    mut v_lhs_924_: *mut LeanObject,
    mut v_rhs_925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_926_: u8 = 0;
    let mut v_r_927_: *mut LeanObject = core::ptr::null_mut();
    v_res_926_ = lean_sarray_dec_eq(v_lhs_924_, v_rhs_925_);
    lean_dec_ref(v_rhs_925_);
    lean_dec_ref(v_lhs_924_);
    v_r_927_ = lean_box((v_res_926_) as usize);
    return v_r_927_;
}
pub unsafe fn l_ByteArray_decEq___boxed(
    mut v_lhs_932_: *mut LeanObject,
    mut v_rhs_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_934_: u8 = 0;
    let mut v_r_935_: *mut LeanObject = core::ptr::null_mut();
    v_res_934_ = lean_sarray_dec_eq(v_lhs_932_, v_rhs_933_);
    lean_dec_ref(v_rhs_933_);
    lean_dec_ref(v_lhs_932_);
    v_r_935_ = lean_box((v_res_934_) as usize);
    return v_r_935_;
}
pub unsafe fn l_ByteArray_instDecidableEq(
    mut v_lhs_936_: *mut LeanObject,
    mut v_rhs_937_: *mut LeanObject,
) -> u8 {
    let mut v___x_938_: u8 = 0;
    v___x_938_ = lean_sarray_dec_eq(v_lhs_936_, v_rhs_937_);
    return v___x_938_;
}
pub unsafe fn l_ByteArray_instDecidableEq___boxed(
    mut v_lhs_939_: *mut LeanObject,
    mut v_rhs_940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_941_: u8 = 0;
    let mut v_r_942_: *mut LeanObject = core::ptr::null_mut();
    v_res_941_ = l_ByteArray_instDecidableEq(v_lhs_939_, v_rhs_940_);
    lean_dec_ref(v_rhs_940_);
    lean_dec_ref(v_lhs_939_);
    v_r_942_ = lean_box((v_res_941_) as usize);
    return v_r_942_;
}
pub unsafe fn _init_l_ByteArray_instInhabited() -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = l_ByteArray_empty;
    return v___x_943_;
}
pub unsafe fn _init_l_ByteArray_instEmptyCollection() -> *mut LeanObject {
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    v___x_944_ = l_ByteArray_empty;
    return v___x_944_;
}
pub unsafe fn l_ByteArray_usize___boxed(mut v_a_946_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_947_: usize = 0;
    let mut v_r_948_: *mut LeanObject = core::ptr::null_mut();
    v_res_947_ = lean_sarray_size(v_a_946_);
    lean_dec_ref(v_a_946_);
    v_r_948_ = lean_box_usize(v_res_947_);
    return v_r_948_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    v___x_973_ = l_ByteArray_uget___auto__1___closed__12;
    v___x_974_ = l_Lean_mkAtom(v___x_973_);
    return v___x_974_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__14() -> *mut LeanObject {
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v___x_975_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__13_once),
        _init_l_ByteArray_uget___auto__1___closed__13,
    );
    v___x_976_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_977_ = lean_array_push(v___x_976_, v___x_975_);
    return v___x_977_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_978_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__14_once),
        _init_l_ByteArray_uget___auto__1___closed__14,
    );
    v___x_979_ = l_ByteArray_uget___auto__1___closed__11;
    v___x_980_ = lean_box(2);
    v___x_981_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_981_, 0, v___x_980_);
    lean_ctor_set(v___x_981_, 1, v___x_979_);
    lean_ctor_set(v___x_981_, 2, v___x_978_);
    return v___x_981_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    v___x_982_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__15_once),
        _init_l_ByteArray_uget___auto__1___closed__15,
    );
    v___x_983_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_984_ = lean_array_push(v___x_983_, v___x_982_);
    return v___x_984_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    v___x_985_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__16_once),
        _init_l_ByteArray_uget___auto__1___closed__16,
    );
    v___x_986_ = l_ByteArray_uget___auto__1___closed__9;
    v___x_987_ = lean_box(2);
    v___x_988_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_988_, 0, v___x_987_);
    lean_ctor_set(v___x_988_, 1, v___x_986_);
    lean_ctor_set(v___x_988_, 2, v___x_985_);
    return v___x_988_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    v___x_989_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__17_once),
        _init_l_ByteArray_uget___auto__1___closed__17,
    );
    v___x_990_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_991_ = lean_array_push(v___x_990_, v___x_989_);
    return v___x_991_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__18_once),
        _init_l_ByteArray_uget___auto__1___closed__18,
    );
    v___x_993_ = l_ByteArray_uget___auto__1___closed__7;
    v___x_994_ = lean_box(2);
    v___x_995_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_995_, 0, v___x_994_);
    lean_ctor_set(v___x_995_, 1, v___x_993_);
    lean_ctor_set(v___x_995_, 2, v___x_992_);
    return v___x_995_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    v___x_996_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__19_once),
        _init_l_ByteArray_uget___auto__1___closed__19,
    );
    v___x_997_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_998_ = lean_array_push(v___x_997_, v___x_996_);
    return v___x_998_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    v___x_999_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__20_once),
        _init_l_ByteArray_uget___auto__1___closed__20,
    );
    v___x_1000_ = l_ByteArray_uget___auto__1___closed__4;
    v___x_1001_ = lean_box(2);
    v___x_1002_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1002_, 0, v___x_1001_);
    lean_ctor_set(v___x_1002_, 1, v___x_1000_);
    lean_ctor_set(v___x_1002_, 2, v___x_999_);
    return v___x_1002_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1() -> *mut LeanObject {
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    v___x_1003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1003_;
}
pub unsafe fn l_ByteArray_uget___boxed(
    mut v_a_1007_: *mut LeanObject,
    mut v_i_1008_: *mut LeanObject,
    mut v_h_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1010_: usize = 0;
    let mut v_res_1011_: u8 = 0;
    let mut v_r_1012_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1010_ = lean_unbox_usize(v_i_1008_);
    lean_dec(v_i_1008_);
    v_res_1011_ = lean_byte_array_uget(v_a_1007_, v_i_boxed_1010_);
    lean_dec_ref(v_a_1007_);
    v_r_1012_ = lean_box((v_res_1011_) as usize);
    return v_r_1012_;
}
pub unsafe fn l_ByteArray_get_x21___boxed(
    mut v_a_00___x40___internal___hyg_1015_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1017_: u8 = 0;
    let mut v_r_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1017_ = lean_byte_array_get(
        v_a_00___x40___internal___hyg_1015_,
        v_a_00___x40___internal___hyg_1016_,
    );
    lean_dec(v_a_00___x40___internal___hyg_1016_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1015_);
    v_r_1018_ = lean_box((v_res_1017_) as usize);
    return v_r_1018_;
}
pub unsafe fn _init_l_ByteArray_get___auto__1() -> *mut LeanObject {
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    v___x_1019_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1019_;
}
pub unsafe fn l_ByteArray_get___boxed(
    mut v_a_1023_: *mut LeanObject,
    mut v_i_1024_: *mut LeanObject,
    mut v_h_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1026_: u8 = 0;
    let mut v_r_1027_: *mut LeanObject = core::ptr::null_mut();
    v_res_1026_ = lean_byte_array_fget(v_a_1023_, v_i_1024_);
    lean_dec(v_i_1024_);
    lean_dec_ref(v_a_1023_);
    v_r_1027_ = lean_box((v_res_1026_) as usize);
    return v_r_1027_;
}
pub unsafe fn l_ByteArray_instGetElemNatUInt8LtSize___lam__0(
    mut v_xs_1028_: *mut LeanObject,
    mut v_i_1029_: *mut LeanObject,
    mut v_h_1030_: *mut LeanObject,
) -> u8 {
    let mut v___x_1031_: u8 = 0;
    v___x_1031_ = lean_byte_array_fget(v_xs_1028_, v_i_1029_);
    return v___x_1031_;
}
pub unsafe fn l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed(
    mut v_xs_1032_: *mut LeanObject,
    mut v_i_1033_: *mut LeanObject,
    mut v_h_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1035_: u8 = 0;
    let mut v_r_1036_: *mut LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_ByteArray_instGetElemNatUInt8LtSize___lam__0(v_xs_1032_, v_i_1033_, v_h_1034_);
    lean_dec(v_i_1033_);
    lean_dec_ref(v_xs_1032_);
    v_r_1036_ = lean_box((v_res_1035_) as usize);
    return v_r_1036_;
}
pub unsafe fn l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(
    mut v_xs_1039_: *mut LeanObject,
    mut v_i_1040_: usize,
    mut v_h_1041_: *mut LeanObject,
) -> u8 {
    let mut v___x_1042_: u8 = 0;
    v___x_1042_ = lean_byte_array_uget(v_xs_1039_, v_i_1040_);
    return v___x_1042_;
}
pub unsafe fn l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed(
    mut v_xs_1043_: *mut LeanObject,
    mut v_i_1044_: *mut LeanObject,
    mut v_h_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1046_: usize = 0;
    let mut v_res_1047_: u8 = 0;
    let mut v_r_1048_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1046_ = lean_unbox_usize(v_i_1044_);
    lean_dec(v_i_1044_);
    v_res_1047_ = l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(
        v_xs_1043_,
        v_i_boxed_1046_,
        v_h_1045_,
    );
    lean_dec_ref(v_xs_1043_);
    v_r_1048_ = lean_box((v_res_1047_) as usize);
    return v_r_1048_;
}
pub unsafe fn l_ByteArray_set_x21___boxed(
    mut v_a_00___x40___internal___hyg_1054_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1055_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_3__boxed_1057_: u8 = 0;
    let mut v_res_1058_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_3__boxed_1057_ =
        (lean_unbox(v_a_00___x40___internal___hyg_1056_) as u8);
    v_res_1058_ = lean_byte_array_set(
        v_a_00___x40___internal___hyg_1054_,
        v_a_00___x40___internal___hyg_1055_,
        v_a_00___x40___internal___hyg_3__boxed_1057_,
    );
    lean_dec(v_a_00___x40___internal___hyg_1055_);
    return v_res_1058_;
}
pub unsafe fn _init_l_ByteArray_set___auto__1() -> *mut LeanObject {
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    v___x_1059_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1059_;
}
pub unsafe fn l_ByteArray_set___boxed(
    mut v_a_1064_: *mut LeanObject,
    mut v_i_1065_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1066_: *mut LeanObject,
    mut v_h_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1068_: u8 = 0;
    let mut v_res_1069_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1068_ =
        (lean_unbox(v_a_00___x40___internal___hyg_1066_) as u8);
    v_res_1069_ = lean_byte_array_fset(
        v_a_1064_,
        v_i_1065_,
        v_a_00___x40___internal___hyg_1__boxed_1068_,
    );
    lean_dec(v_i_1065_);
    return v_res_1069_;
}
pub unsafe fn _init_l_ByteArray_uset___auto__1() -> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1070_;
}
pub unsafe fn l_ByteArray_uset___boxed(
    mut v_a_1075_: *mut LeanObject,
    mut v_i_1076_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1077_: *mut LeanObject,
    mut v_h_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1079_: usize = 0;
    let mut v_a_00___x40___internal___hyg_1__boxed_1080_: u8 = 0;
    let mut v_res_1081_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1079_ = lean_unbox_usize(v_i_1076_);
    lean_dec(v_i_1076_);
    v_a_00___x40___internal___hyg_1__boxed_1080_ =
        (lean_unbox(v_a_00___x40___internal___hyg_1077_) as u8);
    v_res_1081_ = lean_byte_array_uset(
        v_a_1075_,
        v_i_boxed_1079_,
        v_a_00___x40___internal___hyg_1__boxed_1080_,
    );
    return v_res_1081_;
}
pub unsafe fn l_ByteArray_hash___boxed(mut v_a_1083_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1084_: u64 = 0;
    let mut v_r_1085_: *mut LeanObject = core::ptr::null_mut();
    v_res_1084_ = lean_byte_array_hash(v_a_1083_);
    lean_dec_ref(v_a_1083_);
    v_r_1085_ = lean_box_uint64(v_res_1084_);
    return v_r_1085_;
}
pub unsafe fn l_ByteArray_isEmpty(mut v_s_1088_: *mut LeanObject) -> u8 {
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: u8 = 0;
    v___x_1089_ = lean_byte_array_size(v_s_1088_);
    v___x_1090_ = lean_unsigned_to_nat(0);
    v___x_1091_ = lean_nat_dec_eq(v___x_1089_, v___x_1090_);
    return v___x_1091_;
}
pub unsafe fn l_ByteArray_isEmpty___boxed(mut v_s_1092_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1093_: u8 = 0;
    let mut v_r_1094_: *mut LeanObject = core::ptr::null_mut();
    v_res_1093_ = l_ByteArray_isEmpty(v_s_1092_);
    lean_dec_ref(v_s_1092_);
    v_r_1094_ = lean_box((v_res_1093_) as usize);
    return v_r_1094_;
}
pub unsafe fn l_ByteArray_copySlice___boxed(
    mut v_src_1101_: *mut LeanObject,
    mut v_srcOff_1102_: *mut LeanObject,
    mut v_dest_1103_: *mut LeanObject,
    mut v_destOff_1104_: *mut LeanObject,
    mut v_len_1105_: *mut LeanObject,
    mut v_exact_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exact_boxed_1107_: u8 = 0;
    let mut v_res_1108_: *mut LeanObject = core::ptr::null_mut();
    v_exact_boxed_1107_ = (lean_unbox(v_exact_1106_) as u8);
    v_res_1108_ = lean_byte_array_copy_slice(
        v_src_1101_,
        v_srcOff_1102_,
        v_dest_1103_,
        v_destOff_1104_,
        v_len_1105_,
        v_exact_boxed_1107_,
    );
    lean_dec_ref(v_src_1101_);
    return v_res_1108_;
}
pub unsafe fn l_ByteArray_extract(
    mut v_a_1109_: *mut LeanObject,
    mut v_b_1110_: *mut LeanObject,
    mut v_e_1111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_ByteArray_empty;
    v___x_1113_ = lean_unsigned_to_nat(0);
    v___x_1114_ = lean_nat_sub(v_e_1111_, v_b_1110_);
    v___x_1115_ = 1;
    v___x_1116_ = lean_byte_array_copy_slice(
        v_a_1109_,
        v_b_1110_,
        v___x_1112_,
        v___x_1113_,
        v___x_1114_,
        v___x_1115_,
    );
    return v___x_1116_;
}
pub unsafe fn l_ByteArray_extract___boxed(
    mut v_a_1117_: *mut LeanObject,
    mut v_b_1118_: *mut LeanObject,
    mut v_e_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1120_: *mut LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_ByteArray_extract(v_a_1117_, v_b_1118_, v_e_1119_);
    lean_dec(v_e_1119_);
    lean_dec_ref(v_a_1117_);
    return v_res_1120_;
}
pub unsafe fn l_ByteArray_fastAppend(
    mut v_a_1121_: *mut LeanObject,
    mut v_b_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: u8 = 0;
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = lean_unsigned_to_nat(0);
    v___x_1124_ = lean_byte_array_size(v_a_1121_);
    v___x_1125_ = lean_byte_array_size(v_b_1122_);
    v___x_1126_ = 0;
    v___x_1127_ = lean_byte_array_copy_slice(
        v_b_1122_,
        v___x_1123_,
        v_a_1121_,
        v___x_1124_,
        v___x_1125_,
        v___x_1126_,
    );
    return v___x_1127_;
}
pub unsafe fn l_ByteArray_fastAppend___boxed(
    mut v_a_1128_: *mut LeanObject,
    mut v_b_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: *mut LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_ByteArray_fastAppend(v_a_1128_, v_b_1129_);
    lean_dec_ref(v_b_1129_);
    return v_res_1130_;
}
pub unsafe fn l_ByteArray_toList_loop(
    mut v_bs_1133_: *mut LeanObject,
    mut v_i_1134_: *mut LeanObject,
    mut v_r_1135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = lean_byte_array_size(v_bs_1133_);
                v___x_1137_ = lean_nat_dec_lt(v_i_1134_, v___x_1136_);
                if v___x_1137_ == 0 {
                    lean_dec(v_i_1134_);
                    v___x_1138_ = l_List_reverse___redArg(v_r_1135_);
                    return v___x_1138_;
                } else {
                    v___x_1139_ = lean_unsigned_to_nat(1);
                    v___x_1140_ = lean_nat_add(v_i_1134_, v___x_1139_);
                    v___x_1141_ = lean_byte_array_get(v_bs_1133_, v_i_1134_);
                    lean_dec(v_i_1134_);
                    v___x_1142_ = lean_box((v___x_1141_) as usize);
                    v___x_1143_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                    lean_ctor_set(v___x_1143_, 1, v_r_1135_);
                    v_i_1134_ = v___x_1140_;
                    v_r_1135_ = v___x_1143_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_toList_loop___boxed(
    mut v_bs_1145_: *mut LeanObject,
    mut v_i_1146_: *mut LeanObject,
    mut v_r_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_ByteArray_toList_loop(v_bs_1145_, v_i_1146_, v_r_1147_);
    lean_dec_ref(v_bs_1145_);
    return v_res_1148_;
}
pub unsafe fn l_ByteArray_toList(mut v_bs_1149_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    v___x_1150_ = lean_unsigned_to_nat(0);
    v___x_1151_ = lean_box(0);
    v___x_1152_ = l_ByteArray_toList_loop(v_bs_1149_, v___x_1150_, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l_ByteArray_toList___boxed(mut v_bs_1153_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1154_: *mut LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_ByteArray_toList(v_bs_1153_);
    lean_dec_ref(v_bs_1153_);
    return v_res_1154_;
}
pub unsafe fn l_ByteArray_findFinIdx_x3f_loop(
    mut v_a_1155_: *mut LeanObject,
    mut v_p_1156_: *mut LeanObject,
    mut v_i_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: u8 = 0;
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1158_ = lean_byte_array_size(v_a_1155_);
                v___x_1159_ = lean_nat_dec_lt(v_i_1157_, v___x_1158_);
                if v___x_1159_ == 0 {
                    lean_dec(v_i_1157_);
                    lean_dec_ref(v_p_1156_);
                    v___x_1160_ = lean_box(0);
                    return v___x_1160_;
                } else {
                    v___x_1161_ = lean_byte_array_fget(v_a_1155_, v_i_1157_);
                    v___x_1162_ = lean_box((v___x_1161_) as usize);
                    lean_inc_ref(v_p_1156_);
                    v___x_1163_ = lean_apply_1(v_p_1156_, v___x_1162_);
                    v___x_1164_ = (lean_unbox(v___x_1163_) as u8);
                    if v___x_1164_ == 0 {
                        v___x_1165_ = lean_unsigned_to_nat(1);
                        v___x_1166_ = lean_nat_add(v_i_1157_, v___x_1165_);
                        lean_dec(v_i_1157_);
                        v_i_1157_ = v___x_1166_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_p_1156_);
                        v___x_1168_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1168_, 0, v_i_1157_);
                        return v___x_1168_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_findFinIdx_x3f_loop___boxed(
    mut v_a_1169_: *mut LeanObject,
    mut v_p_1170_: *mut LeanObject,
    mut v_i_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1172_: *mut LeanObject = core::ptr::null_mut();
    v_res_1172_ = l_ByteArray_findFinIdx_x3f_loop(v_a_1169_, v_p_1170_, v_i_1171_);
    lean_dec_ref(v_a_1169_);
    return v_res_1172_;
}
pub unsafe fn l_ByteArray_findFinIdx_x3f(
    mut v_a_1173_: *mut LeanObject,
    mut v_p_1174_: *mut LeanObject,
    mut v_start_1175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    v___x_1176_ = l_ByteArray_findFinIdx_x3f_loop(v_a_1173_, v_p_1174_, v_start_1175_);
    return v___x_1176_;
}
pub unsafe fn l_ByteArray_findFinIdx_x3f___boxed(
    mut v_a_1177_: *mut LeanObject,
    mut v_p_1178_: *mut LeanObject,
    mut v_start_1179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1180_: *mut LeanObject = core::ptr::null_mut();
    v_res_1180_ = l_ByteArray_findFinIdx_x3f(v_a_1177_, v_p_1178_, v_start_1179_);
    lean_dec_ref(v_a_1177_);
    return v_res_1180_;
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop(
    mut v_a_1181_: *mut LeanObject,
    mut v_p_1182_: *mut LeanObject,
    mut v_i_1183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1184_ = lean_byte_array_size(v_a_1181_);
                v___x_1185_ = lean_nat_dec_lt(v_i_1183_, v___x_1184_);
                if v___x_1185_ == 0 {
                    lean_dec(v_i_1183_);
                    lean_dec_ref(v_p_1182_);
                    v___x_1186_ = lean_box(0);
                    return v___x_1186_;
                } else {
                    v___x_1187_ = lean_byte_array_fget(v_a_1181_, v_i_1183_);
                    v___x_1188_ = lean_box((v___x_1187_) as usize);
                    lean_inc_ref(v_p_1182_);
                    v___x_1189_ = lean_apply_1(v_p_1182_, v___x_1188_);
                    v___x_1190_ = (lean_unbox(v___x_1189_) as u8);
                    if v___x_1190_ == 0 {
                        v___x_1191_ = lean_unsigned_to_nat(1);
                        v___x_1192_ = lean_nat_add(v_i_1183_, v___x_1191_);
                        lean_dec(v_i_1183_);
                        v_i_1183_ = v___x_1192_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_p_1182_);
                        v___x_1194_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1194_, 0, v_i_1183_);
                        return v___x_1194_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___boxed(
    mut v_a_1195_: *mut LeanObject,
    mut v_p_1196_: *mut LeanObject,
    mut v_i_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1198_: *mut LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_ByteArray_findIdx_x3f_loop(v_a_1195_, v_p_1196_, v_i_1197_);
    lean_dec_ref(v_a_1195_);
    return v_res_1198_;
}
pub unsafe fn l_ByteArray_findIdx_x3f(
    mut v_a_1199_: *mut LeanObject,
    mut v_p_1200_: *mut LeanObject,
    mut v_start_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_ByteArray_findIdx_x3f_loop(v_a_1199_, v_p_1200_, v_start_1201_);
    return v___x_1202_;
}
pub unsafe fn l_ByteArray_findIdx_x3f___boxed(
    mut v_a_1203_: *mut LeanObject,
    mut v_p_1204_: *mut LeanObject,
    mut v_start_1205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1206_: *mut LeanObject = core::ptr::null_mut();
    v_res_1206_ = l_ByteArray_findIdx_x3f(v_a_1203_, v_p_1204_, v_start_1205_);
    lean_dec_ref(v_a_1203_);
    return v_res_1206_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(
    mut v_toApplicative_1207_: *mut LeanObject,
    mut v_i_1208_: *mut LeanObject,
    mut v_inst_1209_: *mut LeanObject,
    mut v_as_1210_: *mut LeanObject,
    mut v_f_1211_: *mut LeanObject,
    mut v_sz_1212_: *mut LeanObject,
    mut v_____do__lift_1213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1214_: usize = 0;
    let mut v_sz_boxed_1215_: usize = 0;
    let mut v_res_1216_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1214_ = lean_unbox_usize(v_i_1208_);
    lean_dec(v_i_1208_);
    v_sz_boxed_1215_ = lean_unbox_usize(v_sz_1212_);
    lean_dec(v_sz_1212_);
    v_res_1216_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(
        v_toApplicative_1207_,
        v_i_boxed_1214_,
        v_inst_1209_,
        v_as_1210_,
        v_f_1211_,
        v_sz_boxed_1215_,
        v_____do__lift_1213_,
    );
    return v_res_1216_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg(
    mut v_inst_1217_: *mut LeanObject,
    mut v_as_1218_: *mut LeanObject,
    mut v_f_1219_: *mut LeanObject,
    mut v_sz_1220_: usize,
    mut v_i_1221_: usize,
    mut v_b_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1223_: u8 = 0;
    v___x_1223_ = lean_usize_dec_lt(v_i_1221_, v_sz_1220_);
    if v___x_1223_ == 0 {
        let mut v_toApplicative_1224_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_1219_);
        lean_dec_ref(v_as_1218_);
        v_toApplicative_1224_ = lean_ctor_get(v_inst_1217_, 0);
        lean_inc_ref(v_toApplicative_1224_);
        lean_dec_ref(v_inst_1217_);
        v_toPure_1225_ = lean_ctor_get(v_toApplicative_1224_, 1);
        lean_inc(v_toPure_1225_);
        lean_dec_ref(v_toApplicative_1224_);
        v___x_1226_ = lean_apply_2(v_toPure_1225_, lean_box(0), v_b_1222_);
        return v___x_1226_;
    } else {
        let mut v_toApplicative_1227_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1231_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1232_: u8 = 0;
        let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1227_ = lean_ctor_get(v_inst_1217_, 0);
        lean_inc_ref(v_toApplicative_1227_);
        v_toBind_1228_ = lean_ctor_get(v_inst_1217_, 1);
        lean_inc(v_toBind_1228_);
        v___x_1229_ = lean_box_usize(v_i_1221_);
        v___x_1230_ = lean_box_usize(v_sz_1220_);
        lean_inc(v_f_1219_);
        lean_inc_ref(v_as_1218_);
        v___f_1231_ = lean_alloc_closure(
            l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___f_1231_, 0, v_toApplicative_1227_);
        lean_closure_set(v___f_1231_, 1, v___x_1229_);
        lean_closure_set(v___f_1231_, 2, v_inst_1217_);
        lean_closure_set(v___f_1231_, 3, v_as_1218_);
        lean_closure_set(v___f_1231_, 4, v_f_1219_);
        lean_closure_set(v___f_1231_, 5, v___x_1230_);
        v_a_1232_ = lean_byte_array_uget(v_as_1218_, v_i_1221_);
        lean_dec_ref(v_as_1218_);
        v___x_1233_ = lean_box((v_a_1232_) as usize);
        v___x_1234_ = lean_apply_2(v_f_1219_, v___x_1233_, v_b_1222_);
        v___x_1235_ = lean_apply_4(
            v_toBind_1228_,
            lean_box(0),
            lean_box(0),
            v___x_1234_,
            v___f_1231_,
        );
        return v___x_1235_;
    }
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg___lam__0(
    mut v_toApplicative_1236_: *mut LeanObject,
    mut v_i_1237_: usize,
    mut v_inst_1238_: *mut LeanObject,
    mut v_as_1239_: *mut LeanObject,
    mut v_f_1240_: *mut LeanObject,
    mut v_sz_1241_: usize,
    mut v_____do__lift_1242_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1242_) == 0 {
        let mut v_a_1243_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_1240_);
        lean_dec_ref(v_as_1239_);
        lean_dec_ref(v_inst_1238_);
        v_a_1243_ = lean_ctor_get(v_____do__lift_1242_, 0);
        lean_inc(v_a_1243_);
        lean_dec_ref_known(v_____do__lift_1242_, 1);
        v_toPure_1244_ = lean_ctor_get(v_toApplicative_1236_, 1);
        lean_inc(v_toPure_1244_);
        lean_dec_ref(v_toApplicative_1236_);
        v___x_1245_ = lean_apply_2(v_toPure_1244_, lean_box(0), v_a_1243_);
        return v___x_1245_;
    } else {
        let mut v_a_1246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: usize = 0;
        let mut v___x_1248_: usize = 0;
        let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_1236_);
        v_a_1246_ = lean_ctor_get(v_____do__lift_1242_, 0);
        lean_inc(v_a_1246_);
        lean_dec_ref_known(v_____do__lift_1242_, 1);
        v___x_1247_ = 1usize;
        v___x_1248_ = lean_usize_add(v_i_1237_, v___x_1247_);
        v___x_1249_ = l_ByteArray_forInUnsafe_loop___redArg(
            v_inst_1238_,
            v_as_1239_,
            v_f_1240_,
            v_sz_1241_,
            v___x_1248_,
            v_a_1246_,
        );
        return v___x_1249_;
    }
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg___boxed(
    mut v_inst_1250_: *mut LeanObject,
    mut v_as_1251_: *mut LeanObject,
    mut v_f_1252_: *mut LeanObject,
    mut v_sz_1253_: *mut LeanObject,
    mut v_i_1254_: *mut LeanObject,
    mut v_b_1255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1256_: usize = 0;
    let mut v_i_boxed_1257_: usize = 0;
    let mut v_res_1258_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1256_ = lean_unbox_usize(v_sz_1253_);
    lean_dec(v_sz_1253_);
    v_i_boxed_1257_ = lean_unbox_usize(v_i_1254_);
    lean_dec(v_i_1254_);
    v_res_1258_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1250_,
        v_as_1251_,
        v_f_1252_,
        v_sz_boxed_1256_,
        v_i_boxed_1257_,
        v_b_1255_,
    );
    return v_res_1258_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop(
    mut v_00_u03b2_1259_: *mut LeanObject,
    mut v_m_1260_: *mut LeanObject,
    mut v_inst_1261_: *mut LeanObject,
    mut v_as_1262_: *mut LeanObject,
    mut v_f_1263_: *mut LeanObject,
    mut v_sz_1264_: usize,
    mut v_i_1265_: usize,
    mut v_b_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1261_,
        v_as_1262_,
        v_f_1263_,
        v_sz_1264_,
        v_i_1265_,
        v_b_1266_,
    );
    return v___x_1267_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___boxed(
    mut v_00_u03b2_1268_: *mut LeanObject,
    mut v_m_1269_: *mut LeanObject,
    mut v_inst_1270_: *mut LeanObject,
    mut v_as_1271_: *mut LeanObject,
    mut v_f_1272_: *mut LeanObject,
    mut v_sz_1273_: *mut LeanObject,
    mut v_i_1274_: *mut LeanObject,
    mut v_b_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1276_: usize = 0;
    let mut v_i_boxed_1277_: usize = 0;
    let mut v_res_1278_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1276_ = lean_unbox_usize(v_sz_1273_);
    lean_dec(v_sz_1273_);
    v_i_boxed_1277_ = lean_unbox_usize(v_i_1274_);
    lean_dec(v_i_1274_);
    v_res_1278_ = l_ByteArray_forInUnsafe_loop(
        v_00_u03b2_1268_,
        v_m_1269_,
        v_inst_1270_,
        v_as_1271_,
        v_f_1272_,
        v_sz_boxed_1276_,
        v_i_boxed_1277_,
        v_b_1275_,
    );
    return v_res_1278_;
}
pub unsafe fn l_ByteArray_forInUnsafe___redArg(
    mut v_inst_1279_: *mut LeanObject,
    mut v_as_1280_: *mut LeanObject,
    mut v_b_1281_: *mut LeanObject,
    mut v_f_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1283_: usize = 0;
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1283_ = lean_sarray_size(v_as_1280_);
    v___x_1284_ = 0usize;
    v___x_1285_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1279_,
        v_as_1280_,
        v_f_1282_,
        v_sz_1283_,
        v___x_1284_,
        v_b_1281_,
    );
    return v___x_1285_;
}
pub unsafe fn l_ByteArray_forInUnsafe(
    mut v_00_u03b2_1286_: *mut LeanObject,
    mut v_m_1287_: *mut LeanObject,
    mut v_inst_1288_: *mut LeanObject,
    mut v_as_1289_: *mut LeanObject,
    mut v_b_1290_: *mut LeanObject,
    mut v_f_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1292_: usize = 0;
    let mut v___x_1293_: usize = 0;
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1292_ = lean_sarray_size(v_as_1289_);
    v___x_1293_ = 0usize;
    v___x_1294_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1288_,
        v_as_1289_,
        v_f_1291_,
        v_sz_1292_,
        v___x_1293_,
        v_b_1290_,
    );
    return v___x_1294_;
}
pub unsafe fn l_ByteArray_forIn_loop___redArg___lam__0___boxed(
    mut v_toPure_1295_: *mut LeanObject,
    mut v_inst_1296_: *mut LeanObject,
    mut v_as_1297_: *mut LeanObject,
    mut v_f_1298_: *mut LeanObject,
    mut v_n_1299_: *mut LeanObject,
    mut v_____do__lift_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1301_: *mut LeanObject = core::ptr::null_mut();
    v_res_1301_ = l_ByteArray_forIn_loop___redArg___lam__0(
        v_toPure_1295_,
        v_inst_1296_,
        v_as_1297_,
        v_f_1298_,
        v_n_1299_,
        v_____do__lift_1300_,
    );
    lean_dec(v_n_1299_);
    return v_res_1301_;
}
pub unsafe fn l_ByteArray_forIn_loop___redArg(
    mut v_inst_1302_: *mut LeanObject,
    mut v_as_1303_: *mut LeanObject,
    mut v_f_1304_: *mut LeanObject,
    mut v_i_1305_: *mut LeanObject,
    mut v_b_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1311_: u8 = 0;
    v_toApplicative_1307_ = lean_ctor_get(v_inst_1302_, 0);
    v_toBind_1308_ = lean_ctor_get(v_inst_1302_, 1);
    lean_inc(v_toBind_1308_);
    v_toPure_1309_ = lean_ctor_get(v_toApplicative_1307_, 1);
    lean_inc(v_toPure_1309_);
    v_zero_1310_ = lean_unsigned_to_nat(0);
    v_isZero_1311_ = lean_nat_dec_eq(v_i_1305_, v_zero_1310_);
    if v_isZero_1311_ == 1 {
        let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_1308_);
        lean_dec(v_f_1304_);
        lean_dec_ref(v_as_1303_);
        lean_dec_ref(v_inst_1302_);
        v___x_1312_ = lean_apply_2(v_toPure_1309_, lean_box(0), v_b_1306_);
        return v___x_1312_;
    } else {
        let mut v_one_1313_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: u8 = 0;
        let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
        v_one_1313_ = lean_unsigned_to_nat(1);
        v_n_1314_ = lean_nat_sub(v_i_1305_, v_one_1313_);
        lean_inc(v_n_1314_);
        lean_inc(v_f_1304_);
        lean_inc_ref(v_as_1303_);
        v___f_1315_ = lean_alloc_closure(
            l_ByteArray_forIn_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_1315_, 0, v_toPure_1309_);
        lean_closure_set(v___f_1315_, 1, v_inst_1302_);
        lean_closure_set(v___f_1315_, 2, v_as_1303_);
        lean_closure_set(v___f_1315_, 3, v_f_1304_);
        lean_closure_set(v___f_1315_, 4, v_n_1314_);
        v___x_1316_ = lean_byte_array_size(v_as_1303_);
        v___x_1317_ = lean_nat_sub(v___x_1316_, v_one_1313_);
        v___x_1318_ = lean_nat_sub(v___x_1317_, v_n_1314_);
        lean_dec(v_n_1314_);
        lean_dec(v___x_1317_);
        v___x_1319_ = lean_byte_array_fget(v_as_1303_, v___x_1318_);
        lean_dec(v___x_1318_);
        lean_dec_ref(v_as_1303_);
        v___x_1320_ = lean_box((v___x_1319_) as usize);
        v___x_1321_ = lean_apply_2(v_f_1304_, v___x_1320_, v_b_1306_);
        v___x_1322_ = lean_apply_4(
            v_toBind_1308_,
            lean_box(0),
            lean_box(0),
            v___x_1321_,
            v___f_1315_,
        );
        return v___x_1322_;
    }
}
pub unsafe fn l_ByteArray_forIn_loop___redArg___lam__0(
    mut v_toPure_1323_: *mut LeanObject,
    mut v_inst_1324_: *mut LeanObject,
    mut v_as_1325_: *mut LeanObject,
    mut v_f_1326_: *mut LeanObject,
    mut v_n_1327_: *mut LeanObject,
    mut v_____do__lift_1328_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1328_) == 0 {
        let mut v_a_1329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_1326_);
        lean_dec_ref(v_as_1325_);
        lean_dec_ref(v_inst_1324_);
        v_a_1329_ = lean_ctor_get(v_____do__lift_1328_, 0);
        lean_inc(v_a_1329_);
        lean_dec_ref_known(v_____do__lift_1328_, 1);
        v___x_1330_ = lean_apply_2(v_toPure_1323_, lean_box(0), v_a_1329_);
        return v___x_1330_;
    } else {
        let mut v_a_1331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1323_);
        v_a_1331_ = lean_ctor_get(v_____do__lift_1328_, 0);
        lean_inc(v_a_1331_);
        lean_dec_ref_known(v_____do__lift_1328_, 1);
        v___x_1332_ = l_ByteArray_forIn_loop___redArg(
            v_inst_1324_,
            v_as_1325_,
            v_f_1326_,
            v_n_1327_,
            v_a_1331_,
        );
        return v___x_1332_;
    }
}
pub unsafe fn l_ByteArray_forIn_loop___redArg___boxed(
    mut v_inst_1333_: *mut LeanObject,
    mut v_as_1334_: *mut LeanObject,
    mut v_f_1335_: *mut LeanObject,
    mut v_i_1336_: *mut LeanObject,
    mut v_b_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1338_: *mut LeanObject = core::ptr::null_mut();
    v_res_1338_ =
        l_ByteArray_forIn_loop___redArg(v_inst_1333_, v_as_1334_, v_f_1335_, v_i_1336_, v_b_1337_);
    lean_dec(v_i_1336_);
    return v_res_1338_;
}
pub unsafe fn l_ByteArray_forIn_loop(
    mut v_00_u03b2_1339_: *mut LeanObject,
    mut v_m_1340_: *mut LeanObject,
    mut v_inst_1341_: *mut LeanObject,
    mut v_as_1342_: *mut LeanObject,
    mut v_f_1343_: *mut LeanObject,
    mut v_i_1344_: *mut LeanObject,
    mut v_h_1345_: *mut LeanObject,
    mut v_b_1346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ =
        l_ByteArray_forIn_loop___redArg(v_inst_1341_, v_as_1342_, v_f_1343_, v_i_1344_, v_b_1346_);
    return v___x_1347_;
}
pub unsafe fn l_ByteArray_forIn_loop___boxed(
    mut v_00_u03b2_1348_: *mut LeanObject,
    mut v_m_1349_: *mut LeanObject,
    mut v_inst_1350_: *mut LeanObject,
    mut v_as_1351_: *mut LeanObject,
    mut v_f_1352_: *mut LeanObject,
    mut v_i_1353_: *mut LeanObject,
    mut v_h_1354_: *mut LeanObject,
    mut v_b_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1356_: *mut LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_ByteArray_forIn_loop(
        v_00_u03b2_1348_,
        v_m_1349_,
        v_inst_1350_,
        v_as_1351_,
        v_f_1352_,
        v_i_1353_,
        v_h_1354_,
        v_b_1355_,
    );
    lean_dec(v_i_1353_);
    return v_res_1356_;
}
pub unsafe fn l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(
    mut v_inst_1357_: *mut LeanObject,
    mut v_00_u03b2_1358_: *mut LeanObject,
    mut v___y_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
    mut v___y_1361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1362_: usize = 0;
    let mut v___x_1363_: usize = 0;
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1362_ = lean_sarray_size(v___y_1359_);
    v___x_1363_ = 0usize;
    v___x_1364_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1357_,
        v___y_1359_,
        v___y_1361_,
        v_sz_1362_,
        v___x_1363_,
        v___y_1360_,
    );
    return v___x_1364_;
}
pub unsafe fn l_ByteArray_instForInUInt8OfMonad___redArg(
    mut v_inst_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1366_: *mut LeanObject = core::ptr::null_mut();
    v___f_1366_ = lean_alloc_closure(
        l_ByteArray_instForInUInt8OfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1366_, 0, v_inst_1365_);
    return v___f_1366_;
}
pub unsafe fn l_ByteArray_instForInUInt8OfMonad(
    mut v_m_1367_: *mut LeanObject,
    mut v_inst_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1369_: *mut LeanObject = core::ptr::null_mut();
    v___f_1369_ = lean_alloc_closure(
        l_ByteArray_instForInUInt8OfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1369_, 0, v_inst_1368_);
    return v___f_1369_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(
    mut v_i_1370_: *mut LeanObject,
    mut v_inst_1371_: *mut LeanObject,
    mut v_f_1372_: *mut LeanObject,
    mut v_as_1373_: *mut LeanObject,
    mut v_stop_1374_: *mut LeanObject,
    mut v_____do__lift_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1376_: usize = 0;
    let mut v_stop_boxed_1377_: usize = 0;
    let mut v_res_1378_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1376_ = lean_unbox_usize(v_i_1370_);
    lean_dec(v_i_1370_);
    v_stop_boxed_1377_ = lean_unbox_usize(v_stop_1374_);
    lean_dec(v_stop_1374_);
    v_res_1378_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(
        v_i_boxed_1376_,
        v_inst_1371_,
        v_f_1372_,
        v_as_1373_,
        v_stop_boxed_1377_,
        v_____do__lift_1375_,
    );
    return v_res_1378_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg(
    mut v_inst_1379_: *mut LeanObject,
    mut v_f_1380_: *mut LeanObject,
    mut v_as_1381_: *mut LeanObject,
    mut v_i_1382_: usize,
    mut v_stop_1383_: usize,
    mut v_b_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1385_: u8 = 0;
    v___x_1385_ = lean_usize_dec_eq(v_i_1382_, v_stop_1383_);
    if v___x_1385_ == 0 {
        let mut v_toBind_1386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: u8 = 0;
        let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1386_ = lean_ctor_get(v_inst_1379_, 1);
        lean_inc(v_toBind_1386_);
        v___x_1387_ = lean_box_usize(v_i_1382_);
        v___x_1388_ = lean_box_usize(v_stop_1383_);
        lean_inc_ref(v_as_1381_);
        lean_inc(v_f_1380_);
        v___f_1389_ = lean_alloc_closure(
            l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_1389_, 0, v___x_1387_);
        lean_closure_set(v___f_1389_, 1, v_inst_1379_);
        lean_closure_set(v___f_1389_, 2, v_f_1380_);
        lean_closure_set(v___f_1389_, 3, v_as_1381_);
        lean_closure_set(v___f_1389_, 4, v___x_1388_);
        v___x_1390_ = lean_byte_array_uget(v_as_1381_, v_i_1382_);
        lean_dec_ref(v_as_1381_);
        v___x_1391_ = lean_box((v___x_1390_) as usize);
        v___x_1392_ = lean_apply_2(v_f_1380_, v_b_1384_, v___x_1391_);
        v___x_1393_ = lean_apply_4(
            v_toBind_1386_,
            lean_box(0),
            lean_box(0),
            v___x_1392_,
            v___f_1389_,
        );
        return v___x_1393_;
    } else {
        let mut v_toApplicative_1394_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_1381_);
        lean_dec(v_f_1380_);
        v_toApplicative_1394_ = lean_ctor_get(v_inst_1379_, 0);
        lean_inc_ref(v_toApplicative_1394_);
        lean_dec_ref(v_inst_1379_);
        v_toPure_1395_ = lean_ctor_get(v_toApplicative_1394_, 1);
        lean_inc(v_toPure_1395_);
        lean_dec_ref(v_toApplicative_1394_);
        v___x_1396_ = lean_apply_2(v_toPure_1395_, lean_box(0), v_b_1384_);
        return v___x_1396_;
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(
    mut v_i_1397_: usize,
    mut v_inst_1398_: *mut LeanObject,
    mut v_f_1399_: *mut LeanObject,
    mut v_as_1400_: *mut LeanObject,
    mut v_stop_1401_: usize,
    mut v_____do__lift_1402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    v___x_1403_ = 1usize;
    v___x_1404_ = lean_usize_add(v_i_1397_, v___x_1403_);
    v___x_1405_ = l_ByteArray_foldlMUnsafe_fold___redArg(
        v_inst_1398_,
        v_f_1399_,
        v_as_1400_,
        v___x_1404_,
        v_stop_1401_,
        v_____do__lift_1402_,
    );
    return v___x_1405_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg___boxed(
    mut v_inst_1406_: *mut LeanObject,
    mut v_f_1407_: *mut LeanObject,
    mut v_as_1408_: *mut LeanObject,
    mut v_i_1409_: *mut LeanObject,
    mut v_stop_1410_: *mut LeanObject,
    mut v_b_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1412_: usize = 0;
    let mut v_stop_boxed_1413_: usize = 0;
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1412_ = lean_unbox_usize(v_i_1409_);
    lean_dec(v_i_1409_);
    v_stop_boxed_1413_ = lean_unbox_usize(v_stop_1410_);
    lean_dec(v_stop_1410_);
    v_res_1414_ = l_ByteArray_foldlMUnsafe_fold___redArg(
        v_inst_1406_,
        v_f_1407_,
        v_as_1408_,
        v_i_boxed_1412_,
        v_stop_boxed_1413_,
        v_b_1411_,
    );
    return v_res_1414_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold(
    mut v_00_u03b2_1415_: *mut LeanObject,
    mut v_m_1416_: *mut LeanObject,
    mut v_inst_1417_: *mut LeanObject,
    mut v_f_1418_: *mut LeanObject,
    mut v_as_1419_: *mut LeanObject,
    mut v_i_1420_: usize,
    mut v_stop_1421_: usize,
    mut v_b_1422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1423_ = l_ByteArray_foldlMUnsafe_fold___redArg(
        v_inst_1417_,
        v_f_1418_,
        v_as_1419_,
        v_i_1420_,
        v_stop_1421_,
        v_b_1422_,
    );
    return v___x_1423_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___boxed(
    mut v_00_u03b2_1424_: *mut LeanObject,
    mut v_m_1425_: *mut LeanObject,
    mut v_inst_1426_: *mut LeanObject,
    mut v_f_1427_: *mut LeanObject,
    mut v_as_1428_: *mut LeanObject,
    mut v_i_1429_: *mut LeanObject,
    mut v_stop_1430_: *mut LeanObject,
    mut v_b_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1432_: usize = 0;
    let mut v_stop_boxed_1433_: usize = 0;
    let mut v_res_1434_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1432_ = lean_unbox_usize(v_i_1429_);
    lean_dec(v_i_1429_);
    v_stop_boxed_1433_ = lean_unbox_usize(v_stop_1430_);
    lean_dec(v_stop_1430_);
    v_res_1434_ = l_ByteArray_foldlMUnsafe_fold(
        v_00_u03b2_1424_,
        v_m_1425_,
        v_inst_1426_,
        v_f_1427_,
        v_as_1428_,
        v_i_boxed_1432_,
        v_stop_boxed_1433_,
        v_b_1431_,
    );
    return v_res_1434_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe___redArg(
    mut v_inst_1435_: *mut LeanObject,
    mut v_f_1436_: *mut LeanObject,
    mut v_init_1437_: *mut LeanObject,
    mut v_as_1438_: *mut LeanObject,
    mut v_start_1439_: *mut LeanObject,
    mut v_stop_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1441_: u8 = 0;
    v___x_1441_ = lean_nat_dec_lt(v_start_1439_, v_stop_1440_);
    if v___x_1441_ == 0 {
        let mut v_toApplicative_1442_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_1438_);
        lean_dec(v_f_1436_);
        v_toApplicative_1442_ = lean_ctor_get(v_inst_1435_, 0);
        lean_inc_ref(v_toApplicative_1442_);
        lean_dec_ref(v_inst_1435_);
        v_toPure_1443_ = lean_ctor_get(v_toApplicative_1442_, 1);
        lean_inc(v_toPure_1443_);
        lean_dec_ref(v_toApplicative_1442_);
        v___x_1444_ = lean_apply_2(v_toPure_1443_, lean_box(0), v_init_1437_);
        return v___x_1444_;
    } else {
        let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: u8 = 0;
        v___x_1445_ = lean_byte_array_size(v_as_1438_);
        v___x_1446_ = lean_nat_dec_le(v_stop_1440_, v___x_1445_);
        if v___x_1446_ == 0 {
            let mut v___x_1447_: u8 = 0;
            v___x_1447_ = lean_nat_dec_lt(v_start_1439_, v___x_1445_);
            if v___x_1447_ == 0 {
                let mut v_toApplicative_1448_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1449_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_as_1438_);
                lean_dec(v_f_1436_);
                v_toApplicative_1448_ = lean_ctor_get(v_inst_1435_, 0);
                lean_inc_ref(v_toApplicative_1448_);
                lean_dec_ref(v_inst_1435_);
                v_toPure_1449_ = lean_ctor_get(v_toApplicative_1448_, 1);
                lean_inc(v_toPure_1449_);
                lean_dec_ref(v_toApplicative_1448_);
                v___x_1450_ = lean_apply_2(v_toPure_1449_, lean_box(0), v_init_1437_);
                return v___x_1450_;
            } else {
                let mut v___x_1451_: usize = 0;
                let mut v___x_1452_: usize = 0;
                let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
                v___x_1451_ = lean_usize_of_nat(v_start_1439_);
                v___x_1452_ = lean_usize_of_nat(v___x_1445_);
                v___x_1453_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v_inst_1435_,
                    v_f_1436_,
                    v_as_1438_,
                    v___x_1451_,
                    v___x_1452_,
                    v_init_1437_,
                );
                return v___x_1453_;
            }
        } else {
            let mut v___x_1454_: usize = 0;
            let mut v___x_1455_: usize = 0;
            let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
            v___x_1454_ = lean_usize_of_nat(v_start_1439_);
            v___x_1455_ = lean_usize_of_nat(v_stop_1440_);
            v___x_1456_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v_inst_1435_,
                v_f_1436_,
                v_as_1438_,
                v___x_1454_,
                v___x_1455_,
                v_init_1437_,
            );
            return v___x_1456_;
        }
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe___redArg___boxed(
    mut v_inst_1457_: *mut LeanObject,
    mut v_f_1458_: *mut LeanObject,
    mut v_init_1459_: *mut LeanObject,
    mut v_as_1460_: *mut LeanObject,
    mut v_start_1461_: *mut LeanObject,
    mut v_stop_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1463_: *mut LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_ByteArray_foldlMUnsafe___redArg(
        v_inst_1457_,
        v_f_1458_,
        v_init_1459_,
        v_as_1460_,
        v_start_1461_,
        v_stop_1462_,
    );
    lean_dec(v_stop_1462_);
    lean_dec(v_start_1461_);
    return v_res_1463_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe(
    mut v_00_u03b2_1464_: *mut LeanObject,
    mut v_m_1465_: *mut LeanObject,
    mut v_inst_1466_: *mut LeanObject,
    mut v_f_1467_: *mut LeanObject,
    mut v_init_1468_: *mut LeanObject,
    mut v_as_1469_: *mut LeanObject,
    mut v_start_1470_: *mut LeanObject,
    mut v_stop_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1472_: u8 = 0;
    v___x_1472_ = lean_nat_dec_lt(v_start_1470_, v_stop_1471_);
    if v___x_1472_ == 0 {
        let mut v_toApplicative_1473_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_1469_);
        lean_dec(v_f_1467_);
        v_toApplicative_1473_ = lean_ctor_get(v_inst_1466_, 0);
        lean_inc_ref(v_toApplicative_1473_);
        lean_dec_ref(v_inst_1466_);
        v_toPure_1474_ = lean_ctor_get(v_toApplicative_1473_, 1);
        lean_inc(v_toPure_1474_);
        lean_dec_ref(v_toApplicative_1473_);
        v___x_1475_ = lean_apply_2(v_toPure_1474_, lean_box(0), v_init_1468_);
        return v___x_1475_;
    } else {
        let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: u8 = 0;
        v___x_1476_ = lean_byte_array_size(v_as_1469_);
        v___x_1477_ = lean_nat_dec_le(v_stop_1471_, v___x_1476_);
        if v___x_1477_ == 0 {
            let mut v___x_1478_: u8 = 0;
            v___x_1478_ = lean_nat_dec_lt(v_start_1470_, v___x_1476_);
            if v___x_1478_ == 0 {
                let mut v_toApplicative_1479_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1480_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_as_1469_);
                lean_dec(v_f_1467_);
                v_toApplicative_1479_ = lean_ctor_get(v_inst_1466_, 0);
                lean_inc_ref(v_toApplicative_1479_);
                lean_dec_ref(v_inst_1466_);
                v_toPure_1480_ = lean_ctor_get(v_toApplicative_1479_, 1);
                lean_inc(v_toPure_1480_);
                lean_dec_ref(v_toApplicative_1479_);
                v___x_1481_ = lean_apply_2(v_toPure_1480_, lean_box(0), v_init_1468_);
                return v___x_1481_;
            } else {
                let mut v___x_1482_: usize = 0;
                let mut v___x_1483_: usize = 0;
                let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
                v___x_1482_ = lean_usize_of_nat(v_start_1470_);
                v___x_1483_ = lean_usize_of_nat(v___x_1476_);
                v___x_1484_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v_inst_1466_,
                    v_f_1467_,
                    v_as_1469_,
                    v___x_1482_,
                    v___x_1483_,
                    v_init_1468_,
                );
                return v___x_1484_;
            }
        } else {
            let mut v___x_1485_: usize = 0;
            let mut v___x_1486_: usize = 0;
            let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
            v___x_1485_ = lean_usize_of_nat(v_start_1470_);
            v___x_1486_ = lean_usize_of_nat(v_stop_1471_);
            v___x_1487_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v_inst_1466_,
                v_f_1467_,
                v_as_1469_,
                v___x_1485_,
                v___x_1486_,
                v_init_1468_,
            );
            return v___x_1487_;
        }
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe___boxed(
    mut v_00_u03b2_1488_: *mut LeanObject,
    mut v_m_1489_: *mut LeanObject,
    mut v_inst_1490_: *mut LeanObject,
    mut v_f_1491_: *mut LeanObject,
    mut v_init_1492_: *mut LeanObject,
    mut v_as_1493_: *mut LeanObject,
    mut v_start_1494_: *mut LeanObject,
    mut v_stop_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1496_: *mut LeanObject = core::ptr::null_mut();
    v_res_1496_ = l_ByteArray_foldlMUnsafe(
        v_00_u03b2_1488_,
        v_m_1489_,
        v_inst_1490_,
        v_f_1491_,
        v_init_1492_,
        v_as_1493_,
        v_start_1494_,
        v_stop_1495_,
    );
    lean_dec(v_stop_1495_);
    lean_dec(v_start_1494_);
    return v_res_1496_;
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg___lam__0___boxed(
    mut v_j_1497_: *mut LeanObject,
    mut v_inst_1498_: *mut LeanObject,
    mut v_f_1499_: *mut LeanObject,
    mut v_as_1500_: *mut LeanObject,
    mut v_stop_1501_: *mut LeanObject,
    mut v_n_1502_: *mut LeanObject,
    mut v_____do__lift_1503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1504_: *mut LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_ByteArray_foldlM_loop___redArg___lam__0(
        v_j_1497_,
        v_inst_1498_,
        v_f_1499_,
        v_as_1500_,
        v_stop_1501_,
        v_n_1502_,
        v_____do__lift_1503_,
    );
    lean_dec(v_n_1502_);
    lean_dec(v_j_1497_);
    return v_res_1504_;
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg(
    mut v_inst_1505_: *mut LeanObject,
    mut v_f_1506_: *mut LeanObject,
    mut v_as_1507_: *mut LeanObject,
    mut v_stop_1508_: *mut LeanObject,
    mut v_i_1509_: *mut LeanObject,
    mut v_j_1510_: *mut LeanObject,
    mut v_b_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1512_: u8 = 0;
    v___x_1512_ = lean_nat_dec_lt(v_j_1510_, v_stop_1508_);
    if v___x_1512_ == 0 {
        let mut v_toApplicative_1513_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_j_1510_);
        lean_dec(v_stop_1508_);
        lean_dec_ref(v_as_1507_);
        lean_dec(v_f_1506_);
        v_toApplicative_1513_ = lean_ctor_get(v_inst_1505_, 0);
        lean_inc_ref(v_toApplicative_1513_);
        lean_dec_ref(v_inst_1505_);
        v_toPure_1514_ = lean_ctor_get(v_toApplicative_1513_, 1);
        lean_inc(v_toPure_1514_);
        lean_dec_ref(v_toApplicative_1513_);
        v___x_1515_ = lean_apply_2(v_toPure_1514_, lean_box(0), v_b_1511_);
        return v___x_1515_;
    } else {
        let mut v_zero_1516_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1517_: u8 = 0;
        v_zero_1516_ = lean_unsigned_to_nat(0);
        v_isZero_1517_ = lean_nat_dec_eq(v_i_1509_, v_zero_1516_);
        if v_isZero_1517_ == 1 {
            let mut v_toApplicative_1518_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_1519_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_j_1510_);
            lean_dec(v_stop_1508_);
            lean_dec_ref(v_as_1507_);
            lean_dec(v_f_1506_);
            v_toApplicative_1518_ = lean_ctor_get(v_inst_1505_, 0);
            lean_inc_ref(v_toApplicative_1518_);
            lean_dec_ref(v_inst_1505_);
            v_toPure_1519_ = lean_ctor_get(v_toApplicative_1518_, 1);
            lean_inc(v_toPure_1519_);
            lean_dec_ref(v_toApplicative_1518_);
            v___x_1520_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_b_1511_);
            return v___x_1520_;
        } else {
            let mut v_toBind_1521_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_1522_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1523_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1524_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1525_: u8 = 0;
            let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
            v_toBind_1521_ = lean_ctor_get(v_inst_1505_, 1);
            lean_inc(v_toBind_1521_);
            v_one_1522_ = lean_unsigned_to_nat(1);
            v_n_1523_ = lean_nat_sub(v_i_1509_, v_one_1522_);
            lean_inc_ref(v_as_1507_);
            lean_inc(v_f_1506_);
            lean_inc(v_j_1510_);
            v___f_1524_ = lean_alloc_closure(
                l_ByteArray_foldlM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
                7,
                6,
            );
            lean_closure_set(v___f_1524_, 0, v_j_1510_);
            lean_closure_set(v___f_1524_, 1, v_inst_1505_);
            lean_closure_set(v___f_1524_, 2, v_f_1506_);
            lean_closure_set(v___f_1524_, 3, v_as_1507_);
            lean_closure_set(v___f_1524_, 4, v_stop_1508_);
            lean_closure_set(v___f_1524_, 5, v_n_1523_);
            v___x_1525_ = lean_byte_array_fget(v_as_1507_, v_j_1510_);
            lean_dec(v_j_1510_);
            lean_dec_ref(v_as_1507_);
            v___x_1526_ = lean_box((v___x_1525_) as usize);
            v___x_1527_ = lean_apply_2(v_f_1506_, v_b_1511_, v___x_1526_);
            v___x_1528_ = lean_apply_4(
                v_toBind_1521_,
                lean_box(0),
                lean_box(0),
                v___x_1527_,
                v___f_1524_,
            );
            return v___x_1528_;
        }
    }
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg___lam__0(
    mut v_j_1529_: *mut LeanObject,
    mut v_inst_1530_: *mut LeanObject,
    mut v_f_1531_: *mut LeanObject,
    mut v_as_1532_: *mut LeanObject,
    mut v_stop_1533_: *mut LeanObject,
    mut v_n_1534_: *mut LeanObject,
    mut v_____do__lift_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    v___x_1536_ = lean_unsigned_to_nat(1);
    v___x_1537_ = lean_nat_add(v_j_1529_, v___x_1536_);
    v___x_1538_ = l_ByteArray_foldlM_loop___redArg(
        v_inst_1530_,
        v_f_1531_,
        v_as_1532_,
        v_stop_1533_,
        v_n_1534_,
        v___x_1537_,
        v_____do__lift_1535_,
    );
    return v___x_1538_;
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg___boxed(
    mut v_inst_1539_: *mut LeanObject,
    mut v_f_1540_: *mut LeanObject,
    mut v_as_1541_: *mut LeanObject,
    mut v_stop_1542_: *mut LeanObject,
    mut v_i_1543_: *mut LeanObject,
    mut v_j_1544_: *mut LeanObject,
    mut v_b_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1546_: *mut LeanObject = core::ptr::null_mut();
    v_res_1546_ = l_ByteArray_foldlM_loop___redArg(
        v_inst_1539_,
        v_f_1540_,
        v_as_1541_,
        v_stop_1542_,
        v_i_1543_,
        v_j_1544_,
        v_b_1545_,
    );
    lean_dec(v_i_1543_);
    return v_res_1546_;
}
pub unsafe fn l_ByteArray_foldlM_loop(
    mut v_00_u03b2_1547_: *mut LeanObject,
    mut v_m_1548_: *mut LeanObject,
    mut v_inst_1549_: *mut LeanObject,
    mut v_f_1550_: *mut LeanObject,
    mut v_as_1551_: *mut LeanObject,
    mut v_stop_1552_: *mut LeanObject,
    mut v_h_1553_: *mut LeanObject,
    mut v_i_1554_: *mut LeanObject,
    mut v_j_1555_: *mut LeanObject,
    mut v_b_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_ByteArray_foldlM_loop___redArg(
        v_inst_1549_,
        v_f_1550_,
        v_as_1551_,
        v_stop_1552_,
        v_i_1554_,
        v_j_1555_,
        v_b_1556_,
    );
    return v___x_1557_;
}
pub unsafe fn l_ByteArray_foldlM_loop___boxed(
    mut v_00_u03b2_1558_: *mut LeanObject,
    mut v_m_1559_: *mut LeanObject,
    mut v_inst_1560_: *mut LeanObject,
    mut v_f_1561_: *mut LeanObject,
    mut v_as_1562_: *mut LeanObject,
    mut v_stop_1563_: *mut LeanObject,
    mut v_h_1564_: *mut LeanObject,
    mut v_i_1565_: *mut LeanObject,
    mut v_j_1566_: *mut LeanObject,
    mut v_b_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1568_: *mut LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_ByteArray_foldlM_loop(
        v_00_u03b2_1558_,
        v_m_1559_,
        v_inst_1560_,
        v_f_1561_,
        v_as_1562_,
        v_stop_1563_,
        v_h_1564_,
        v_i_1565_,
        v_j_1566_,
        v_b_1567_,
    );
    lean_dec(v_i_1565_);
    return v_res_1568_;
}
pub unsafe fn l_ByteArray_foldl___redArg___lam__0(
    mut v_f_1569_: *mut LeanObject,
    mut v_x1_1570_: *mut LeanObject,
    mut v_x2_1571_: u8,
) -> *mut LeanObject {
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    v___x_1572_ = lean_box((v_x2_1571_) as usize);
    v___x_1573_ = lean_apply_2(v_f_1569_, v_x1_1570_, v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn l_ByteArray_foldl___redArg___lam__0___boxed(
    mut v_f_1574_: *mut LeanObject,
    mut v_x1_1575_: *mut LeanObject,
    mut v_x2_1576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_190__boxed_1577_: u8 = 0;
    let mut v_res_1578_: *mut LeanObject = core::ptr::null_mut();
    v_x2_190__boxed_1577_ = (lean_unbox(v_x2_1576_) as u8);
    v_res_1578_ = l_ByteArray_foldl___redArg___lam__0(v_f_1574_, v_x1_1575_, v_x2_190__boxed_1577_);
    return v_res_1578_;
}
pub unsafe fn l_ByteArray_foldl___redArg(
    mut v_f_1598_: *mut LeanObject,
    mut v_init_1599_: *mut LeanObject,
    mut v_as_1600_: *mut LeanObject,
    mut v_start_1601_: *mut LeanObject,
    mut v_stop_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: u8 = 0;
    v___x_1603_ = l_ByteArray_foldl___redArg___closed__9;
    v___x_1604_ = lean_nat_dec_lt(v_start_1601_, v_stop_1602_);
    if v___x_1604_ == 0 {
        lean_dec_ref(v_as_1600_);
        lean_dec(v_f_1598_);
        return v_init_1599_;
    } else {
        let mut v___f_1605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: u8 = 0;
        v___f_1605_ = lean_alloc_closure(
            l_ByteArray_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1605_, 0, v_f_1598_);
        v___x_1606_ = lean_byte_array_size(v_as_1600_);
        v___x_1607_ = lean_nat_dec_le(v_stop_1602_, v___x_1606_);
        if v___x_1607_ == 0 {
            let mut v___x_1608_: u8 = 0;
            v___x_1608_ = lean_nat_dec_lt(v_start_1601_, v___x_1606_);
            if v___x_1608_ == 0 {
                lean_dec_ref(v___f_1605_);
                lean_dec_ref(v_as_1600_);
                return v_init_1599_;
            } else {
                let mut v___x_1609_: usize = 0;
                let mut v___x_1610_: usize = 0;
                let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
                v___x_1609_ = lean_usize_of_nat(v_start_1601_);
                v___x_1610_ = lean_usize_of_nat(v___x_1606_);
                v___x_1611_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v___x_1603_,
                    v___f_1605_,
                    v_as_1600_,
                    v___x_1609_,
                    v___x_1610_,
                    v_init_1599_,
                );
                return v___x_1611_;
            }
        } else {
            let mut v___x_1612_: usize = 0;
            let mut v___x_1613_: usize = 0;
            let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
            v___x_1612_ = lean_usize_of_nat(v_start_1601_);
            v___x_1613_ = lean_usize_of_nat(v_stop_1602_);
            v___x_1614_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v___x_1603_,
                v___f_1605_,
                v_as_1600_,
                v___x_1612_,
                v___x_1613_,
                v_init_1599_,
            );
            return v___x_1614_;
        }
    }
}
pub unsafe fn l_ByteArray_foldl___redArg___boxed(
    mut v_f_1615_: *mut LeanObject,
    mut v_init_1616_: *mut LeanObject,
    mut v_as_1617_: *mut LeanObject,
    mut v_start_1618_: *mut LeanObject,
    mut v_stop_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1620_: *mut LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_ByteArray_foldl___redArg(
        v_f_1615_,
        v_init_1616_,
        v_as_1617_,
        v_start_1618_,
        v_stop_1619_,
    );
    lean_dec(v_stop_1619_);
    lean_dec(v_start_1618_);
    return v_res_1620_;
}
pub unsafe fn l_ByteArray_foldl(
    mut v_00_u03b2_1621_: *mut LeanObject,
    mut v_f_1622_: *mut LeanObject,
    mut v_init_1623_: *mut LeanObject,
    mut v_as_1624_: *mut LeanObject,
    mut v_start_1625_: *mut LeanObject,
    mut v_stop_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    v___x_1627_ = l_ByteArray_foldl___redArg___closed__9;
    v___x_1628_ = lean_nat_dec_lt(v_start_1625_, v_stop_1626_);
    if v___x_1628_ == 0 {
        lean_dec_ref(v_as_1624_);
        lean_dec(v_f_1622_);
        return v_init_1623_;
    } else {
        let mut v___f_1629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: u8 = 0;
        v___f_1629_ = lean_alloc_closure(
            l_ByteArray_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1629_, 0, v_f_1622_);
        v___x_1630_ = lean_byte_array_size(v_as_1624_);
        v___x_1631_ = lean_nat_dec_le(v_stop_1626_, v___x_1630_);
        if v___x_1631_ == 0 {
            let mut v___x_1632_: u8 = 0;
            v___x_1632_ = lean_nat_dec_lt(v_start_1625_, v___x_1630_);
            if v___x_1632_ == 0 {
                lean_dec_ref(v___f_1629_);
                lean_dec_ref(v_as_1624_);
                return v_init_1623_;
            } else {
                let mut v___x_1633_: usize = 0;
                let mut v___x_1634_: usize = 0;
                let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
                v___x_1633_ = lean_usize_of_nat(v_start_1625_);
                v___x_1634_ = lean_usize_of_nat(v___x_1630_);
                v___x_1635_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v___x_1627_,
                    v___f_1629_,
                    v_as_1624_,
                    v___x_1633_,
                    v___x_1634_,
                    v_init_1623_,
                );
                return v___x_1635_;
            }
        } else {
            let mut v___x_1636_: usize = 0;
            let mut v___x_1637_: usize = 0;
            let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
            v___x_1636_ = lean_usize_of_nat(v_start_1625_);
            v___x_1637_ = lean_usize_of_nat(v_stop_1626_);
            v___x_1638_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v___x_1627_,
                v___f_1629_,
                v_as_1624_,
                v___x_1636_,
                v___x_1637_,
                v_init_1623_,
            );
            return v___x_1638_;
        }
    }
}
pub unsafe fn l_ByteArray_foldl___boxed(
    mut v_00_u03b2_1639_: *mut LeanObject,
    mut v_f_1640_: *mut LeanObject,
    mut v_init_1641_: *mut LeanObject,
    mut v_as_1642_: *mut LeanObject,
    mut v_start_1643_: *mut LeanObject,
    mut v_stop_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1645_: *mut LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_ByteArray_foldl(
        v_00_u03b2_1639_,
        v_f_1640_,
        v_init_1641_,
        v_as_1642_,
        v_start_1643_,
        v_stop_1644_,
    );
    lean_dec(v_stop_1644_);
    lean_dec(v_start_1643_);
    return v_res_1645_;
}
pub unsafe fn _init_l_ByteArray_instInhabitedIterator_default___closed__0() -> *mut LeanObject {
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    v___x_1646_ = lean_unsigned_to_nat(0);
    v___x_1647_ = l_ByteArray_empty;
    v___x_1648_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1648_, 0, v___x_1647_);
    lean_ctor_set(v___x_1648_, 1, v___x_1646_);
    return v___x_1648_;
}
pub unsafe fn _init_l_ByteArray_instInhabitedIterator_default() -> *mut LeanObject {
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    v___x_1649_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_instInhabitedIterator_default___closed__0),
        core::ptr::addr_of_mut!(l_ByteArray_instInhabitedIterator_default___closed__0_once),
        _init_l_ByteArray_instInhabitedIterator_default___closed__0,
    );
    return v___x_1649_;
}
pub unsafe fn _init_l_ByteArray_instInhabitedIterator() -> *mut LeanObject {
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_ByteArray_instInhabitedIterator_default;
    return v___x_1650_;
}
pub unsafe fn l_ByteArray_mkIterator(mut v_arr_1651_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    v___x_1652_ = lean_unsigned_to_nat(0);
    v___x_1653_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1653_, 0, v_arr_1651_);
    lean_ctor_set(v___x_1653_, 1, v___x_1652_);
    return v___x_1653_;
}
pub unsafe fn l_ByteArray_iter(mut v_arr_1654_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_ByteArray_mkIterator(v_arr_1654_);
    return v___x_1655_;
}
pub unsafe fn l_ByteArray_instSizeOfIterator___lam__0(
    mut v_i_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    v_array_1657_ = lean_ctor_get(v_i_1656_, 0);
    v_idx_1658_ = lean_ctor_get(v_i_1656_, 1);
    v___x_1659_ = lean_byte_array_size(v_array_1657_);
    v___x_1660_ = lean_nat_sub(v___x_1659_, v_idx_1658_);
    return v___x_1660_;
}
pub unsafe fn l_ByteArray_instSizeOfIterator___lam__0___boxed(
    mut v_i_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1662_: *mut LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_ByteArray_instSizeOfIterator___lam__0(v_i_1661_);
    lean_dec_ref(v_i_1661_);
    return v_res_1662_;
}
pub unsafe fn l_ByteArray_Iterator_remainingBytes(
    mut v_x_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    v_array_1666_ = lean_ctor_get(v_x_1665_, 0);
    v_idx_1667_ = lean_ctor_get(v_x_1665_, 1);
    v___x_1668_ = lean_byte_array_size(v_array_1666_);
    v___x_1669_ = lean_nat_sub(v___x_1668_, v_idx_1667_);
    return v___x_1669_;
}
pub unsafe fn l_ByteArray_Iterator_remainingBytes___boxed(
    mut v_x_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1671_: *mut LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_ByteArray_Iterator_remainingBytes(v_x_1670_);
    lean_dec_ref(v_x_1670_);
    return v_res_1671_;
}
pub unsafe fn l_ByteArray_Iterator_pos(mut v_self_1672_: *mut LeanObject) -> *mut LeanObject {
    let mut v_idx_1673_: *mut LeanObject = core::ptr::null_mut();
    v_idx_1673_ = lean_ctor_get(v_self_1672_, 1);
    lean_inc(v_idx_1673_);
    return v_idx_1673_;
}
pub unsafe fn l_ByteArray_Iterator_pos___boxed(
    mut v_self_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1675_: *mut LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_ByteArray_Iterator_pos(v_self_1674_);
    lean_dec_ref(v_self_1674_);
    return v_res_1675_;
}
pub unsafe fn l_ByteArray_Iterator_atEnd(mut v_x_1676_: *mut LeanObject) -> u8 {
    let mut v_array_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    v_array_1677_ = lean_ctor_get(v_x_1676_, 0);
    v_idx_1678_ = lean_ctor_get(v_x_1676_, 1);
    v___x_1679_ = lean_byte_array_size(v_array_1677_);
    v___x_1680_ = lean_nat_dec_le(v___x_1679_, v_idx_1678_);
    return v___x_1680_;
}
pub unsafe fn l_ByteArray_Iterator_atEnd___boxed(
    mut v_x_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1682_: u8 = 0;
    let mut v_r_1683_: *mut LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_ByteArray_Iterator_atEnd(v_x_1681_);
    lean_dec_ref(v_x_1681_);
    v_r_1683_ = lean_box((v_res_1682_) as usize);
    return v_r_1683_;
}
pub unsafe fn _init_l_ByteArray_Iterator_curr___closed__0() -> u8 {
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v___x_1684_ = lean_unsigned_to_nat(0);
    v___x_1685_ = lean_uint8_of_nat(v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn l_ByteArray_Iterator_curr(mut v_x_1686_: *mut LeanObject) -> u8 {
    let mut v_array_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    v_array_1687_ = lean_ctor_get(v_x_1686_, 0);
    v_idx_1688_ = lean_ctor_get(v_x_1686_, 1);
    v___x_1689_ = lean_byte_array_size(v_array_1687_);
    v___x_1690_ = lean_nat_dec_lt(v_idx_1688_, v___x_1689_);
    if v___x_1690_ == 0 {
        let mut v___x_1691_: u8 = 0;
        v___x_1691_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_ByteArray_Iterator_curr___closed__0),
            core::ptr::addr_of_mut!(l_ByteArray_Iterator_curr___closed__0_once),
            _init_l_ByteArray_Iterator_curr___closed__0,
        );
        return v___x_1691_;
    } else {
        let mut v___x_1692_: u8 = 0;
        v___x_1692_ = lean_byte_array_fget(v_array_1687_, v_idx_1688_);
        return v___x_1692_;
    }
}
pub unsafe fn l_ByteArray_Iterator_curr___boxed(mut v_x_1693_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1694_: u8 = 0;
    let mut v_r_1695_: *mut LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_ByteArray_Iterator_curr(v_x_1693_);
    lean_dec_ref(v_x_1693_);
    v_r_1695_ = lean_box((v_res_1694_) as usize);
    return v_r_1695_;
}
pub unsafe fn l_ByteArray_Iterator_next(mut v_x_1696_: *mut LeanObject) -> *mut LeanObject {
    let mut v_array_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1697_ = lean_ctor_get(v_x_1696_, 0);
                v_idx_1698_ = lean_ctor_get(v_x_1696_, 1);
                v_isSharedCheck_1707_ = (!lean_is_exclusive(v_x_1696_)) as u8;
                if v_isSharedCheck_1707_ == 0 {
                    v___x_1700_ = v_x_1696_;
                    v_isShared_1701_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1698_);
                    lean_inc(v_array_1697_);
                    lean_dec(v_x_1696_);
                    v___x_1700_ = lean_box(0);
                    v_isShared_1701_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = lean_unsigned_to_nat(1);
                v___x_1703_ = lean_nat_add(v_idx_1698_, v___x_1702_);
                lean_dec(v_idx_1698_);
                if v_isShared_1701_ == 0 {
                    lean_ctor_set(v___x_1700_, 1, v___x_1703_);
                    v___x_1705_ = v___x_1700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_array_1697_);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1703_);
                    v___x_1705_ = v_reuseFailAlloc_1706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_prev(mut v_x_1708_: *mut LeanObject) -> *mut LeanObject {
    let mut v_array_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1709_ = lean_ctor_get(v_x_1708_, 0);
                v_idx_1710_ = lean_ctor_get(v_x_1708_, 1);
                v_isSharedCheck_1719_ = (!lean_is_exclusive(v_x_1708_)) as u8;
                if v_isSharedCheck_1719_ == 0 {
                    v___x_1712_ = v_x_1708_;
                    v_isShared_1713_ = v_isSharedCheck_1719_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1710_);
                    lean_inc(v_array_1709_);
                    lean_dec(v_x_1708_);
                    v___x_1712_ = lean_box(0);
                    v_isShared_1713_ = v_isSharedCheck_1719_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1714_ = lean_unsigned_to_nat(1);
                v___x_1715_ = lean_nat_sub(v_idx_1710_, v___x_1714_);
                lean_dec(v_idx_1710_);
                if v_isShared_1713_ == 0 {
                    lean_ctor_set(v___x_1712_, 1, v___x_1715_);
                    v___x_1717_ = v___x_1712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_array_1709_);
                    lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1715_);
                    v___x_1717_ = v_reuseFailAlloc_1718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_hasNext(mut v_x_1720_: *mut LeanObject) -> u8 {
    let mut v_array_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    v_array_1721_ = lean_ctor_get(v_x_1720_, 0);
    v_idx_1722_ = lean_ctor_get(v_x_1720_, 1);
    v___x_1723_ = lean_byte_array_size(v_array_1721_);
    v___x_1724_ = lean_nat_dec_lt(v_idx_1722_, v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_ByteArray_Iterator_hasNext___boxed(
    mut v_x_1725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1726_: u8 = 0;
    let mut v_r_1727_: *mut LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_ByteArray_Iterator_hasNext(v_x_1725_);
    lean_dec_ref(v_x_1725_);
    v_r_1727_ = lean_box((v_res_1726_) as usize);
    return v_r_1727_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___redArg(
    mut v_x_1728_: *mut LeanObject,
    mut v_h__1_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    v_array_1730_ = lean_ctor_get(v_x_1728_, 0);
    lean_inc_ref(v_array_1730_);
    v_idx_1731_ = lean_ctor_get(v_x_1728_, 1);
    lean_inc(v_idx_1731_);
    lean_dec_ref(v_x_1728_);
    v___x_1732_ = lean_apply_2(v_h__1_1729_, v_array_1730_, v_idx_1731_);
    return v___x_1732_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(
    mut v_motive_1733_: *mut LeanObject,
    mut v_x_1734_: *mut LeanObject,
    mut v_h__1_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    v_array_1736_ = lean_ctor_get(v_x_1734_, 0);
    lean_inc_ref(v_array_1736_);
    v_idx_1737_ = lean_ctor_get(v_x_1734_, 1);
    lean_inc(v_idx_1737_);
    lean_dec_ref(v_x_1734_);
    v___x_1738_ = lean_apply_2(v_h__1_1735_, v_array_1736_, v_idx_1737_);
    return v___x_1738_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27___redArg(mut v_it_1739_: *mut LeanObject) -> u8 {
    let mut v_array_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    v_array_1740_ = lean_ctor_get(v_it_1739_, 0);
    v_idx_1741_ = lean_ctor_get(v_it_1739_, 1);
    v___x_1742_ = lean_byte_array_fget(v_array_1740_, v_idx_1741_);
    return v___x_1742_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27___redArg___boxed(
    mut v_it_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1744_: u8 = 0;
    let mut v_r_1745_: *mut LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_1743_);
    lean_dec_ref(v_it_1743_);
    v_r_1745_ = lean_box((v_res_1744_) as usize);
    return v_r_1745_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27(
    mut v_it_1746_: *mut LeanObject,
    mut v_h_1747_: *mut LeanObject,
) -> u8 {
    let mut v_array_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u8 = 0;
    v_array_1748_ = lean_ctor_get(v_it_1746_, 0);
    v_idx_1749_ = lean_ctor_get(v_it_1746_, 1);
    v___x_1750_ = lean_byte_array_fget(v_array_1748_, v_idx_1749_);
    return v___x_1750_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27___boxed(
    mut v_it_1751_: *mut LeanObject,
    mut v_h_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1753_: u8 = 0;
    let mut v_r_1754_: *mut LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_ByteArray_Iterator_curr_x27(v_it_1751_, v_h_1752_);
    lean_dec_ref(v_it_1751_);
    v_r_1754_ = lean_box((v_res_1753_) as usize);
    return v_r_1754_;
}
pub unsafe fn l_ByteArray_Iterator_next_x27___redArg(
    mut v_it_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1756_ = lean_ctor_get(v_it_1755_, 0);
                v_idx_1757_ = lean_ctor_get(v_it_1755_, 1);
                v_isSharedCheck_1766_ = (!lean_is_exclusive(v_it_1755_)) as u8;
                if v_isSharedCheck_1766_ == 0 {
                    v___x_1759_ = v_it_1755_;
                    v_isShared_1760_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1757_);
                    lean_inc(v_array_1756_);
                    lean_dec(v_it_1755_);
                    v___x_1759_ = lean_box(0);
                    v_isShared_1760_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1761_ = lean_unsigned_to_nat(1);
                v___x_1762_ = lean_nat_add(v_idx_1757_, v___x_1761_);
                lean_dec(v_idx_1757_);
                if v_isShared_1760_ == 0 {
                    lean_ctor_set(v___x_1759_, 1, v___x_1762_);
                    v___x_1764_ = v___x_1759_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_array_1756_);
                    lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
                    v___x_1764_ = v_reuseFailAlloc_1765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_next_x27(
    mut v_it_1767_: *mut LeanObject,
    mut v___h_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1769_ = lean_ctor_get(v_it_1767_, 0);
                v_idx_1770_ = lean_ctor_get(v_it_1767_, 1);
                v_isSharedCheck_1779_ = (!lean_is_exclusive(v_it_1767_)) as u8;
                if v_isSharedCheck_1779_ == 0 {
                    v___x_1772_ = v_it_1767_;
                    v_isShared_1773_ = v_isSharedCheck_1779_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1770_);
                    lean_inc(v_array_1769_);
                    lean_dec(v_it_1767_);
                    v___x_1772_ = lean_box(0);
                    v_isShared_1773_ = v_isSharedCheck_1779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1774_ = lean_unsigned_to_nat(1);
                v___x_1775_ = lean_nat_add(v_idx_1770_, v___x_1774_);
                lean_dec(v_idx_1770_);
                if v_isShared_1773_ == 0 {
                    lean_ctor_set(v___x_1772_, 1, v___x_1775_);
                    v___x_1777_ = v___x_1772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_array_1769_);
                    lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1775_);
                    v___x_1777_ = v_reuseFailAlloc_1778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_hasPrev(mut v_x_1780_: *mut LeanObject) -> u8 {
    let mut v_idx_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    v_idx_1781_ = lean_ctor_get(v_x_1780_, 1);
    v___x_1782_ = lean_unsigned_to_nat(0);
    v___x_1783_ = lean_nat_dec_lt(v___x_1782_, v_idx_1781_);
    return v___x_1783_;
}
pub unsafe fn l_ByteArray_Iterator_hasPrev___boxed(
    mut v_x_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1785_: u8 = 0;
    let mut v_r_1786_: *mut LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_ByteArray_Iterator_hasPrev(v_x_1784_);
    lean_dec_ref(v_x_1784_);
    v_r_1786_ = lean_box((v_res_1785_) as usize);
    return v_r_1786_;
}
pub unsafe fn l_ByteArray_Iterator_toEnd(mut v_x_1787_: *mut LeanObject) -> *mut LeanObject {
    let mut v_array_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_unused_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1788_ = lean_ctor_get(v_x_1787_, 0);
                v_isSharedCheck_1796_ = (!lean_is_exclusive(v_x_1787_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v_unused_1797_ = lean_ctor_get(v_x_1787_, 1);
                    lean_dec(v_unused_1797_);
                    v___x_1790_ = v_x_1787_;
                    v_isShared_1791_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_array_1788_);
                    lean_dec(v_x_1787_);
                    v___x_1790_ = lean_box(0);
                    v_isShared_1791_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1792_ = lean_byte_array_size(v_array_1788_);
                if v_isShared_1791_ == 0 {
                    lean_ctor_set(v___x_1790_, 1, v___x_1792_);
                    v___x_1794_ = v___x_1790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_array_1788_);
                    lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1792_);
                    v___x_1794_ = v_reuseFailAlloc_1795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_forward(
    mut v_x_1798_: *mut LeanObject,
    mut v_x_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1804_: u8 = 0;
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1800_ = lean_ctor_get(v_x_1798_, 0);
                v_idx_1801_ = lean_ctor_get(v_x_1798_, 1);
                v_isSharedCheck_1809_ = (!lean_is_exclusive(v_x_1798_)) as u8;
                if v_isSharedCheck_1809_ == 0 {
                    v___x_1803_ = v_x_1798_;
                    v_isShared_1804_ = v_isSharedCheck_1809_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1801_);
                    lean_inc(v_array_1800_);
                    lean_dec(v_x_1798_);
                    v___x_1803_ = lean_box(0);
                    v_isShared_1804_ = v_isSharedCheck_1809_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1805_ = lean_nat_add(v_idx_1801_, v_x_1799_);
                lean_dec(v_idx_1801_);
                if v_isShared_1804_ == 0 {
                    lean_ctor_set(v___x_1803_, 1, v___x_1805_);
                    v___x_1807_ = v___x_1803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_array_1800_);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1805_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_forward___boxed(
    mut v_x_1810_: *mut LeanObject,
    mut v_x_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_res_1812_ = l_ByteArray_Iterator_forward(v_x_1810_, v_x_1811_);
    lean_dec(v_x_1811_);
    return v_res_1812_;
}
pub unsafe fn l_ByteArray_Iterator_nextn(
    mut v_a_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1815_ = lean_ctor_get(v_a_1813_, 0);
                v_idx_1816_ = lean_ctor_get(v_a_1813_, 1);
                v_isSharedCheck_1824_ = (!lean_is_exclusive(v_a_1813_)) as u8;
                if v_isSharedCheck_1824_ == 0 {
                    v___x_1818_ = v_a_1813_;
                    v_isShared_1819_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1816_);
                    lean_inc(v_array_1815_);
                    lean_dec(v_a_1813_);
                    v___x_1818_ = lean_box(0);
                    v_isShared_1819_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1820_ = lean_nat_add(v_idx_1816_, v_a_1814_);
                lean_dec(v_idx_1816_);
                if v_isShared_1819_ == 0 {
                    lean_ctor_set(v___x_1818_, 1, v___x_1820_);
                    v___x_1822_ = v___x_1818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_array_1815_);
                    lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1820_);
                    v___x_1822_ = v_reuseFailAlloc_1823_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_nextn___boxed(
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1827_: *mut LeanObject = core::ptr::null_mut();
    v_res_1827_ = l_ByteArray_Iterator_nextn(v_a_1825_, v_a_1826_);
    lean_dec(v_a_1826_);
    return v_res_1827_;
}
pub unsafe fn l_ByteArray_Iterator_prevn(
    mut v_x_1828_: *mut LeanObject,
    mut v_x_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1830_ = lean_ctor_get(v_x_1828_, 0);
                v_idx_1831_ = lean_ctor_get(v_x_1828_, 1);
                v_isSharedCheck_1839_ = (!lean_is_exclusive(v_x_1828_)) as u8;
                if v_isSharedCheck_1839_ == 0 {
                    v___x_1833_ = v_x_1828_;
                    v_isShared_1834_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1831_);
                    lean_inc(v_array_1830_);
                    lean_dec(v_x_1828_);
                    v___x_1833_ = lean_box(0);
                    v_isShared_1834_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1835_ = lean_nat_sub(v_idx_1831_, v_x_1829_);
                lean_dec(v_idx_1831_);
                if v_isShared_1834_ == 0 {
                    lean_ctor_set(v___x_1833_, 1, v___x_1835_);
                    v___x_1837_ = v___x_1833_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_array_1830_);
                    lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1835_);
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_prevn___boxed(
    mut v_x_1840_: *mut LeanObject,
    mut v_x_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1842_: *mut LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_ByteArray_Iterator_prevn(v_x_1840_, v_x_1841_);
    lean_dec(v_x_1841_);
    return v_res_1842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ByteArray_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_ByteArray_instInhabited = _init_l_ByteArray_instInhabited();
    lean_mark_persistent(l_ByteArray_instInhabited);
    l_ByteArray_instEmptyCollection = _init_l_ByteArray_instEmptyCollection();
    lean_mark_persistent(l_ByteArray_instEmptyCollection);
    l_ByteArray_instInhabitedIterator_default = _init_l_ByteArray_instInhabitedIterator_default();
    lean_mark_persistent(l_ByteArray_instInhabitedIterator_default);
    l_ByteArray_instInhabitedIterator = _init_l_ByteArray_instInhabitedIterator();
    lean_mark_persistent(l_ByteArray_instInhabitedIterator);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ByteArray_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_ByteArray_uget___auto__1 = _init_l_ByteArray_uget___auto__1();
    lean_mark_persistent(l_ByteArray_uget___auto__1);
    l_ByteArray_get___auto__1 = _init_l_ByteArray_get___auto__1();
    lean_mark_persistent(l_ByteArray_get___auto__1);
    l_ByteArray_set___auto__1 = _init_l_ByteArray_set___auto__1();
    lean_mark_persistent(l_ByteArray_set___auto__1);
    l_ByteArray_uset___auto__1 = _init_l_ByteArray_uset___auto__1();
    lean_mark_persistent(l_ByteArray_uset___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_ByteArray_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_ByteArray_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_ByteArray_Basic(builtin);
}
