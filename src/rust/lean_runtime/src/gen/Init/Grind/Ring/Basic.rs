// Lean compiler output
// Module: Init.Grind.Ring.Basic
// Imports: Init.Grind.Module.Basic Init.ByCases Init.Data.Int.DivMod.Lemmas Init.Data.Int.LemmasAux Init.Data.Int.Pow Init.Data.Nat.Div.Lemmas Init.Data.Nat.Lemmas Init.Omega Init.RCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Div::Lemmas::{
    initialize_Init_Data_Nat_Div_Lemmas, runtime_initialize_Init_Data_Nat_Div_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Grind::Module::Basic::{
    initialize_Init_Grind_Module_Basic, runtime_initialize_Init_Grind_Module_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_utf8_byte_size,
};
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value:
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
    m_data: [105, 110, 116, 114, 111, 115, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value)
            as *mut crate::leanh::LeanObject,
        3278676588586250010 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18_value:
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
    m_data: [59, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21_value)
            as *mut crate::leanh::LeanObject,
        3294379458557754569 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 102, 108, 0],
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_Semiring_ofNat__succ___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_Ring_intCast__ofNat___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_Ring_intCast__neg___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5665407707378192681 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value:
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
    m_data: [97, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value)
            as *mut crate::leanh::LeanObject,
        7839396180116328695 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 119, 83, 101, 113, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15_value)
            as *mut crate::leanh::LeanObject,
        11075965128531316786 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [114, 119, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25_value:
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
    m_data: [114, 119, 82, 117, 108, 101, 83, 101, 113, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25_value)
            as *mut crate::leanh::LeanObject,
        7234207980690920618 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27_value:
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
    m_data: [91, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30_value:
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
    m_data: [114, 119, 82, 117, 108, 101, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30_value)
            as *mut crate::leanh::LeanObject,
        8860902369834437795 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [109, 117, 108, 95, 99, 111, 109, 109, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32_value)
            as *mut crate::leanh::LeanObject,
        12672327883528904144 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40_value:
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
    m_data: [44, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 117, 108, 95, 111, 110, 101, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value)
            as *mut crate::leanh::LeanObject,
        14938772321304097465 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53_value:
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
    m_data: [93, 0],
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_CommSemiring_one__mul___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [122, 101, 114, 111, 95, 109, 117, 108, 0],
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7783155206718462231 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_CommSemiring_mul__zero___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value:
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
    m_data: [98, 0],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10300200614825825839 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value:
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
    m_data: [99, 0],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value)
            as *mut crate::leanh::LeanObject,
        388469914488256294 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [108, 101, 102, 116, 95, 100, 105, 115, 116, 114, 105, 98, 0],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value)
            as *mut crate::leanh::LeanObject,
        17937649215359900029 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27_value)
            as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_CommSemiring_right__distrib___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10;
    v___x_607_ = l_Lean_mkAtom(v___x_606_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12,
    );
    v___x_609_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_610_ = lean_array_push(v___x_609_, v___x_608_);
    return v___x_610_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
    v___x_616_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13,
    );
    v___x_617_ = lean_array_push(v___x_616_, v___x_615_);
    return v___x_617_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15,
    );
    v___x_619_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11;
    v___x_620_ = crate::leanh::lean_box(2);
    v___x_621_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_621_, 0, v___x_620_);
    crate::leanh::lean_ctor_set(v___x_621_, 1, v___x_619_);
    crate::leanh::lean_ctor_set(v___x_621_, 2, v___x_618_);
    return v___x_621_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16,
    );
    v___x_623_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_624_ = lean_array_push(v___x_623_, v___x_622_);
    return v___x_624_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_626_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18;
    v___x_627_ = l_Lean_mkAtom(v___x_626_);
    return v___x_627_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19,
    );
    v___x_629_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17,
    );
    v___x_630_ = lean_array_push(v___x_629_, v___x_628_);
    return v___x_630_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23;
    v___x_639_ = l_Lean_mkAtom(v___x_638_);
    return v___x_639_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24,
    );
    v___x_641_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_642_ = lean_array_push(v___x_641_, v___x_640_);
    return v___x_642_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25,
    );
    v___x_644_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22;
    v___x_645_ = crate::leanh::lean_box(2);
    v___x_646_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_646_, 0, v___x_645_);
    crate::leanh::lean_ctor_set(v___x_646_, 1, v___x_644_);
    crate::leanh::lean_ctor_set(v___x_646_, 2, v___x_643_);
    return v___x_646_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_647_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26,
    );
    v___x_648_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20,
    );
    v___x_649_ = lean_array_push(v___x_648_, v___x_647_);
    return v___x_649_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27,
    );
    v___x_651_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_652_ = crate::leanh::lean_box(2);
    v___x_653_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_653_, 0, v___x_652_);
    crate::leanh::lean_ctor_set(v___x_653_, 1, v___x_651_);
    crate::leanh::lean_ctor_set(v___x_653_, 2, v___x_650_);
    return v___x_653_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28,
    );
    v___x_655_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_656_ = lean_array_push(v___x_655_, v___x_654_);
    return v___x_656_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29,
    );
    v___x_658_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7;
    v___x_659_ = crate::leanh::lean_box(2);
    v___x_660_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_660_, 0, v___x_659_);
    crate::leanh::lean_ctor_set(v___x_660_, 1, v___x_658_);
    crate::leanh::lean_ctor_set(v___x_660_, 2, v___x_657_);
    return v___x_660_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_661_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30,
    );
    v___x_662_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_663_ = lean_array_push(v___x_662_, v___x_661_);
    return v___x_663_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31,
    );
    v___x_665_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4;
    v___x_666_ = crate::leanh::lean_box(2);
    v___x_667_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_667_, 0, v___x_666_);
    crate::leanh::lean_ctor_set(v___x_667_, 1, v___x_665_);
    crate::leanh::lean_ctor_set(v___x_667_, 2, v___x_664_);
    return v___x_667_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam() -> *mut crate::leanh::LeanObject
{
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32,
    );
    return v___x_668_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32,
    );
    return v___x_669_;
}
pub unsafe fn _init_l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32,
    );
    return v___x_670_;
}
pub unsafe fn _init_l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32,
    );
    return v___x_671_;
}
pub unsafe fn _init_l_Lean_Grind_Ring_intCast__ofNat___autoParam() -> *mut crate::leanh::LeanObject
{
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32,
    );
    return v___x_672_;
}
pub unsafe fn _init_l_Lean_Grind_Ring_intCast__neg___autoParam() -> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32,
    );
    return v___x_673_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0;
    v___x_681_ = l_Lean_mkAtom(v___x_680_);
    return v___x_681_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2,
    );
    v___x_683_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_684_ = lean_array_push(v___x_683_, v___x_682_);
    return v___x_684_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_686_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4;
    v___x_687_ = lean_string_utf8_byte_size(v___x_686_);
    return v___x_687_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5,
    );
    v___x_689_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_690_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4;
    v___x_691_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_691_, 0, v___x_690_);
    crate::leanh::lean_ctor_set(v___x_691_, 1, v___x_689_);
    crate::leanh::lean_ctor_set(v___x_691_, 2, v___x_688_);
    return v___x_691_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_694_ = crate::leanh::lean_box(0);
    v___x_695_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7;
    v___x_696_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6,
    );
    v___x_697_ = crate::leanh::lean_box(2);
    v___x_698_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_698_, 0, v___x_697_);
    crate::leanh::lean_ctor_set(v___x_698_, 1, v___x_696_);
    crate::leanh::lean_ctor_set(v___x_698_, 2, v___x_695_);
    crate::leanh::lean_ctor_set(v___x_698_, 3, v___x_694_);
    return v___x_698_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8,
    );
    v___x_700_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_701_ = lean_array_push(v___x_700_, v___x_699_);
    return v___x_701_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9,
    );
    v___x_703_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_704_ = crate::leanh::lean_box(2);
    v___x_705_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_705_, 0, v___x_704_);
    crate::leanh::lean_ctor_set(v___x_705_, 1, v___x_703_);
    crate::leanh::lean_ctor_set(v___x_705_, 2, v___x_702_);
    return v___x_705_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10,
    );
    v___x_707_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3,
    );
    v___x_708_ = lean_array_push(v___x_707_, v___x_706_);
    return v___x_708_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11,
    );
    v___x_710_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1;
    v___x_711_ = crate::leanh::lean_box(2);
    v___x_712_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_712_, 0, v___x_711_);
    crate::leanh::lean_ctor_set(v___x_712_, 1, v___x_710_);
    crate::leanh::lean_ctor_set(v___x_712_, 2, v___x_709_);
    return v___x_712_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12,
    );
    v___x_714_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_715_ = lean_array_push(v___x_714_, v___x_713_);
    return v___x_715_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19,
    );
    v___x_717_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13,
    );
    v___x_718_ = lean_array_push(v___x_717_, v___x_716_);
    return v___x_718_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_726_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17;
    v___x_727_ = l_Lean_mkAtom(v___x_726_);
    return v___x_727_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18,
    );
    v___x_729_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_730_ = lean_array_push(v___x_729_, v___x_728_);
    return v___x_730_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
    v___x_738_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_739_ = lean_array_push(v___x_738_, v___x_737_);
    return v___x_739_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22,
    );
    v___x_741_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21;
    v___x_742_ = crate::leanh::lean_box(2);
    v___x_743_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_743_, 0, v___x_742_);
    crate::leanh::lean_ctor_set(v___x_743_, 1, v___x_741_);
    crate::leanh::lean_ctor_set(v___x_743_, 2, v___x_740_);
    return v___x_743_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23,
    );
    v___x_745_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19,
    );
    v___x_746_ = lean_array_push(v___x_745_, v___x_744_);
    return v___x_746_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27;
    v___x_755_ = l_Lean_mkAtom(v___x_754_);
    return v___x_755_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28,
    );
    v___x_757_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_758_ = lean_array_push(v___x_757_, v___x_756_);
    return v___x_758_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32;
    v___x_767_ = lean_string_utf8_byte_size(v___x_766_);
    return v___x_767_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33,
    );
    v___x_769_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_770_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32;
    v___x_771_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_771_, 0, v___x_770_);
    crate::leanh::lean_ctor_set(v___x_771_, 1, v___x_769_);
    crate::leanh::lean_ctor_set(v___x_771_, 2, v___x_768_);
    return v___x_771_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = crate::leanh::lean_box(0);
    v___x_775_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35;
    v___x_776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34,
    );
    v___x_777_ = crate::leanh::lean_box(2);
    v___x_778_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_777_);
    crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_776_);
    crate::leanh::lean_ctor_set(v___x_778_, 2, v___x_775_);
    crate::leanh::lean_ctor_set(v___x_778_, 3, v___x_774_);
    return v___x_778_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36,
    );
    v___x_780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22,
    );
    v___x_781_ = lean_array_push(v___x_780_, v___x_779_);
    return v___x_781_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_782_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37,
    );
    v___x_783_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31;
    v___x_784_ = crate::leanh::lean_box(2);
    v___x_785_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_785_, 0, v___x_784_);
    crate::leanh::lean_ctor_set(v___x_785_, 1, v___x_783_);
    crate::leanh::lean_ctor_set(v___x_785_, 2, v___x_782_);
    return v___x_785_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_786_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38,
    );
    v___x_787_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_788_ = lean_array_push(v___x_787_, v___x_786_);
    return v___x_788_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40;
    v___x_791_ = l_Lean_mkAtom(v___x_790_);
    return v___x_791_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41,
    );
    v___x_793_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39,
    );
    v___x_794_ = lean_array_push(v___x_793_, v___x_792_);
    return v___x_794_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43;
    v___x_797_ = lean_string_utf8_byte_size(v___x_796_);
    return v___x_797_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44,
    );
    v___x_799_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_800_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43;
    v___x_801_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_801_, 0, v___x_800_);
    crate::leanh::lean_ctor_set(v___x_801_, 1, v___x_799_);
    crate::leanh::lean_ctor_set(v___x_801_, 2, v___x_798_);
    return v___x_801_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = crate::leanh::lean_box(0);
    v___x_805_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46;
    v___x_806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45,
    );
    v___x_807_ = crate::leanh::lean_box(2);
    v___x_808_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_808_, 0, v___x_807_);
    crate::leanh::lean_ctor_set(v___x_808_, 1, v___x_806_);
    crate::leanh::lean_ctor_set(v___x_808_, 2, v___x_805_);
    crate::leanh::lean_ctor_set(v___x_808_, 3, v___x_804_);
    return v___x_808_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47,
    );
    v___x_810_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22,
    );
    v___x_811_ = lean_array_push(v___x_810_, v___x_809_);
    return v___x_811_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49()
-> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48,
    );
    v___x_813_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31;
    v___x_814_ = crate::leanh::lean_box(2);
    v___x_815_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_814_);
    crate::leanh::lean_ctor_set(v___x_815_, 1, v___x_813_);
    crate::leanh::lean_ctor_set(v___x_815_, 2, v___x_812_);
    return v___x_815_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49,
    );
    v___x_817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42,
    );
    v___x_818_ = lean_array_push(v___x_817_, v___x_816_);
    return v___x_818_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50,
    );
    v___x_820_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_821_ = crate::leanh::lean_box(2);
    v___x_822_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_821_);
    crate::leanh::lean_ctor_set(v___x_822_, 1, v___x_820_);
    crate::leanh::lean_ctor_set(v___x_822_, 2, v___x_819_);
    return v___x_822_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52()
-> *mut crate::leanh::LeanObject {
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51,
    );
    v___x_824_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29,
    );
    v___x_825_ = lean_array_push(v___x_824_, v___x_823_);
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53;
    v___x_828_ = l_Lean_mkAtom(v___x_827_);
    return v___x_828_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55()
-> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54,
    );
    v___x_830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52,
    );
    v___x_831_ = lean_array_push(v___x_830_, v___x_829_);
    return v___x_831_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56()
-> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55,
    );
    v___x_833_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26;
    v___x_834_ = crate::leanh::lean_box(2);
    v___x_835_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_835_, 0, v___x_834_);
    crate::leanh::lean_ctor_set(v___x_835_, 1, v___x_833_);
    crate::leanh::lean_ctor_set(v___x_835_, 2, v___x_832_);
    return v___x_835_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56,
    );
    v___x_837_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24,
    );
    v___x_838_ = lean_array_push(v___x_837_, v___x_836_);
    return v___x_838_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
    v___x_840_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57,
    );
    v___x_841_ = lean_array_push(v___x_840_, v___x_839_);
    return v___x_841_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59()
-> *mut crate::leanh::LeanObject {
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_842_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58,
    );
    v___x_843_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16;
    v___x_844_ = crate::leanh::lean_box(2);
    v___x_845_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_845_, 0, v___x_844_);
    crate::leanh::lean_ctor_set(v___x_845_, 1, v___x_843_);
    crate::leanh::lean_ctor_set(v___x_845_, 2, v___x_842_);
    return v___x_845_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59,
    );
    v___x_847_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14,
    );
    v___x_848_ = lean_array_push(v___x_847_, v___x_846_);
    return v___x_848_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60,
    );
    v___x_850_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_851_ = crate::leanh::lean_box(2);
    v___x_852_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_852_, 0, v___x_851_);
    crate::leanh::lean_ctor_set(v___x_852_, 1, v___x_850_);
    crate::leanh::lean_ctor_set(v___x_852_, 2, v___x_849_);
    return v___x_852_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62()
-> *mut crate::leanh::LeanObject {
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61,
    );
    v___x_854_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_855_ = lean_array_push(v___x_854_, v___x_853_);
    return v___x_855_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_856_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62,
    );
    v___x_857_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7;
    v___x_858_ = crate::leanh::lean_box(2);
    v___x_859_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_859_, 0, v___x_858_);
    crate::leanh::lean_ctor_set(v___x_859_, 1, v___x_857_);
    crate::leanh::lean_ctor_set(v___x_859_, 2, v___x_856_);
    return v___x_859_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64()
-> *mut crate::leanh::LeanObject {
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63,
    );
    v___x_861_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_862_ = lean_array_push(v___x_861_, v___x_860_);
    return v___x_862_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65()
-> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64,
    );
    v___x_864_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4;
    v___x_865_ = crate::leanh::lean_box(2);
    v___x_866_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_865_);
    crate::leanh::lean_ctor_set(v___x_866_, 1, v___x_864_);
    crate::leanh::lean_ctor_set(v___x_866_, 2, v___x_863_);
    return v___x_866_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_one__mul___autoParam() -> *mut crate::leanh::LeanObject
{
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65,
    );
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0;
    v___x_870_ = lean_string_utf8_byte_size(v___x_869_);
    return v___x_870_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1,
    );
    v___x_872_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_873_ = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0;
    v___x_874_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_874_, 0, v___x_873_);
    crate::leanh::lean_ctor_set(v___x_874_, 1, v___x_872_);
    crate::leanh::lean_ctor_set(v___x_874_, 2, v___x_871_);
    return v___x_874_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = crate::leanh::lean_box(0);
    v___x_878_ = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3;
    v___x_879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2,
    );
    v___x_880_ = crate::leanh::lean_box(2);
    v___x_881_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_881_, 0, v___x_880_);
    crate::leanh::lean_ctor_set(v___x_881_, 1, v___x_879_);
    crate::leanh::lean_ctor_set(v___x_881_, 2, v___x_878_);
    crate::leanh::lean_ctor_set(v___x_881_, 3, v___x_877_);
    return v___x_881_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4,
    );
    v___x_883_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22,
    );
    v___x_884_ = lean_array_push(v___x_883_, v___x_882_);
    return v___x_884_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5,
    );
    v___x_886_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31;
    v___x_887_ = crate::leanh::lean_box(2);
    v___x_888_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_888_, 0, v___x_887_);
    crate::leanh::lean_ctor_set(v___x_888_, 1, v___x_886_);
    crate::leanh::lean_ctor_set(v___x_888_, 2, v___x_885_);
    return v___x_888_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6,
    );
    v___x_890_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42,
    );
    v___x_891_ = lean_array_push(v___x_890_, v___x_889_);
    return v___x_891_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7,
    );
    v___x_893_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_894_ = crate::leanh::lean_box(2);
    v___x_895_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_895_, 0, v___x_894_);
    crate::leanh::lean_ctor_set(v___x_895_, 1, v___x_893_);
    crate::leanh::lean_ctor_set(v___x_895_, 2, v___x_892_);
    return v___x_895_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8,
    );
    v___x_897_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29,
    );
    v___x_898_ = lean_array_push(v___x_897_, v___x_896_);
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54,
    );
    v___x_900_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9,
    );
    v___x_901_ = lean_array_push(v___x_900_, v___x_899_);
    return v___x_901_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_902_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10,
    );
    v___x_903_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26;
    v___x_904_ = crate::leanh::lean_box(2);
    v___x_905_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_905_, 0, v___x_904_);
    crate::leanh::lean_ctor_set(v___x_905_, 1, v___x_903_);
    crate::leanh::lean_ctor_set(v___x_905_, 2, v___x_902_);
    return v___x_905_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11,
    );
    v___x_907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24,
    );
    v___x_908_ = lean_array_push(v___x_907_, v___x_906_);
    return v___x_908_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
    v___x_910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12,
    );
    v___x_911_ = lean_array_push(v___x_910_, v___x_909_);
    return v___x_911_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13,
    );
    v___x_913_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16;
    v___x_914_ = crate::leanh::lean_box(2);
    v___x_915_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_915_, 0, v___x_914_);
    crate::leanh::lean_ctor_set(v___x_915_, 1, v___x_913_);
    crate::leanh::lean_ctor_set(v___x_915_, 2, v___x_912_);
    return v___x_915_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14,
    );
    v___x_917_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14,
    );
    v___x_918_ = lean_array_push(v___x_917_, v___x_916_);
    return v___x_918_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15,
    );
    v___x_920_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_921_ = crate::leanh::lean_box(2);
    v___x_922_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_922_, 0, v___x_921_);
    crate::leanh::lean_ctor_set(v___x_922_, 1, v___x_920_);
    crate::leanh::lean_ctor_set(v___x_922_, 2, v___x_919_);
    return v___x_922_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_923_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16,
    );
    v___x_924_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_925_ = lean_array_push(v___x_924_, v___x_923_);
    return v___x_925_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_926_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17,
    );
    v___x_927_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7;
    v___x_928_ = crate::leanh::lean_box(2);
    v___x_929_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_929_, 0, v___x_928_);
    crate::leanh::lean_ctor_set(v___x_929_, 1, v___x_927_);
    crate::leanh::lean_ctor_set(v___x_929_, 2, v___x_926_);
    return v___x_929_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_930_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18,
    );
    v___x_931_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_932_ = lean_array_push(v___x_931_, v___x_930_);
    return v___x_932_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19,
    );
    v___x_934_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4;
    v___x_935_ = crate::leanh::lean_box(2);
    v___x_936_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_935_);
    crate::leanh::lean_ctor_set(v___x_936_, 1, v___x_934_);
    crate::leanh::lean_ctor_set(v___x_936_, 2, v___x_933_);
    return v___x_936_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_937_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20_once),
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20,
    );
    return v___x_937_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_939_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0;
    v___x_940_ = lean_string_utf8_byte_size(v___x_939_);
    return v___x_940_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1,
    );
    v___x_942_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_943_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0;
    v___x_944_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_944_, 0, v___x_943_);
    crate::leanh::lean_ctor_set(v___x_944_, 1, v___x_942_);
    crate::leanh::lean_ctor_set(v___x_944_, 2, v___x_941_);
    return v___x_944_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = crate::leanh::lean_box(0);
    v___x_948_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3;
    v___x_949_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2,
    );
    v___x_950_ = crate::leanh::lean_box(2);
    v___x_951_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_951_, 0, v___x_950_);
    crate::leanh::lean_ctor_set(v___x_951_, 1, v___x_949_);
    crate::leanh::lean_ctor_set(v___x_951_, 2, v___x_948_);
    crate::leanh::lean_ctor_set(v___x_951_, 3, v___x_947_);
    return v___x_951_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4,
    );
    v___x_953_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9,
    );
    v___x_954_ = lean_array_push(v___x_953_, v___x_952_);
    return v___x_954_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_956_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6;
    v___x_957_ = lean_string_utf8_byte_size(v___x_956_);
    return v___x_957_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7,
    );
    v___x_959_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_960_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6;
    v___x_961_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_961_, 0, v___x_960_);
    crate::leanh::lean_ctor_set(v___x_961_, 1, v___x_959_);
    crate::leanh::lean_ctor_set(v___x_961_, 2, v___x_958_);
    return v___x_961_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ = crate::leanh::lean_box(0);
    v___x_965_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9;
    v___x_966_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8,
    );
    v___x_967_ = crate::leanh::lean_box(2);
    v___x_968_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_968_, 0, v___x_967_);
    crate::leanh::lean_ctor_set(v___x_968_, 1, v___x_966_);
    crate::leanh::lean_ctor_set(v___x_968_, 2, v___x_965_);
    crate::leanh::lean_ctor_set(v___x_968_, 3, v___x_964_);
    return v___x_968_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10,
    );
    v___x_970_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5,
    );
    v___x_971_ = lean_array_push(v___x_970_, v___x_969_);
    return v___x_971_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11,
    );
    v___x_973_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_974_ = crate::leanh::lean_box(2);
    v___x_975_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_975_, 0, v___x_974_);
    crate::leanh::lean_ctor_set(v___x_975_, 1, v___x_973_);
    crate::leanh::lean_ctor_set(v___x_975_, 2, v___x_972_);
    return v___x_975_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12,
    );
    v___x_977_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3,
    );
    v___x_978_ = lean_array_push(v___x_977_, v___x_976_);
    return v___x_978_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13,
    );
    v___x_980_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1;
    v___x_981_ = crate::leanh::lean_box(2);
    v___x_982_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
    crate::leanh::lean_ctor_set(v___x_982_, 1, v___x_980_);
    crate::leanh::lean_ctor_set(v___x_982_, 2, v___x_979_);
    return v___x_982_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14,
    );
    v___x_984_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_985_ = lean_array_push(v___x_984_, v___x_983_);
    return v___x_985_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once),
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19,
    );
    v___x_987_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15,
    );
    v___x_988_ = lean_array_push(v___x_987_, v___x_986_);
    return v___x_988_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_990_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17;
    v___x_991_ = lean_string_utf8_byte_size(v___x_990_);
    return v___x_991_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18,
    );
    v___x_993_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_994_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17;
    v___x_995_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_994_);
    crate::leanh::lean_ctor_set(v___x_995_, 1, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_995_, 2, v___x_992_);
    return v___x_995_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = crate::leanh::lean_box(0);
    v___x_999_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20;
    v___x_1000_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19,
    );
    v___x_1001_ = crate::leanh::lean_box(2);
    v___x_1002_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1002_, 0, v___x_1001_);
    crate::leanh::lean_ctor_set(v___x_1002_, 1, v___x_1000_);
    crate::leanh::lean_ctor_set(v___x_1002_, 2, v___x_999_);
    crate::leanh::lean_ctor_set(v___x_1002_, 3, v___x_998_);
    return v___x_1002_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21,
    );
    v___x_1004_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22,
    );
    v___x_1005_ = lean_array_push(v___x_1004_, v___x_1003_);
    return v___x_1005_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1006_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22,
    );
    v___x_1007_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31;
    v___x_1008_ = crate::leanh::lean_box(2);
    v___x_1009_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1009_, 0, v___x_1008_);
    crate::leanh::lean_ctor_set(v___x_1009_, 1, v___x_1007_);
    crate::leanh::lean_ctor_set(v___x_1009_, 2, v___x_1006_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23,
    );
    v___x_1011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42,
    );
    v___x_1012_ = lean_array_push(v___x_1011_, v___x_1010_);
    return v___x_1012_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41,
    );
    v___x_1014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24,
    );
    v___x_1015_ = lean_array_push(v___x_1014_, v___x_1013_);
    return v___x_1015_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36,
    );
    v___x_1024_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_1025_ = lean_array_push(v___x_1024_, v___x_1023_);
    return v___x_1025_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10,
    );
    v___x_1027_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_1028_ = lean_array_push(v___x_1027_, v___x_1026_);
    return v___x_1028_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1029_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30,
    );
    v___x_1030_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_1031_ = crate::leanh::lean_box(2);
    v___x_1032_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1032_, 0, v___x_1031_);
    crate::leanh::lean_ctor_set(v___x_1032_, 1, v___x_1030_);
    crate::leanh::lean_ctor_set(v___x_1032_, 2, v___x_1029_);
    return v___x_1032_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31,
    );
    v___x_1034_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29,
    );
    v___x_1035_ = lean_array_push(v___x_1034_, v___x_1033_);
    return v___x_1035_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32,
    );
    v___x_1037_ = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28;
    v___x_1038_ = crate::leanh::lean_box(2);
    v___x_1039_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1039_, 0, v___x_1038_);
    crate::leanh::lean_ctor_set(v___x_1039_, 1, v___x_1037_);
    crate::leanh::lean_ctor_set(v___x_1039_, 2, v___x_1036_);
    return v___x_1039_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33,
    );
    v___x_1041_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22,
    );
    v___x_1042_ = lean_array_push(v___x_1041_, v___x_1040_);
    return v___x_1042_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34,
    );
    v___x_1044_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31;
    v___x_1045_ = crate::leanh::lean_box(2);
    v___x_1046_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1046_, 0, v___x_1045_);
    crate::leanh::lean_ctor_set(v___x_1046_, 1, v___x_1044_);
    crate::leanh::lean_ctor_set(v___x_1046_, 2, v___x_1043_);
    return v___x_1046_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1047_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35,
    );
    v___x_1048_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25,
    );
    v___x_1049_ = lean_array_push(v___x_1048_, v___x_1047_);
    return v___x_1049_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41,
    );
    v___x_1051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36,
    );
    v___x_1052_ = lean_array_push(v___x_1051_, v___x_1050_);
    return v___x_1052_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35,
    );
    v___x_1054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37,
    );
    v___x_1055_ = lean_array_push(v___x_1054_, v___x_1053_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1056_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38,
    );
    v___x_1057_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_1058_ = crate::leanh::lean_box(2);
    v___x_1059_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1059_, 0, v___x_1058_);
    crate::leanh::lean_ctor_set(v___x_1059_, 1, v___x_1057_);
    crate::leanh::lean_ctor_set(v___x_1059_, 2, v___x_1056_);
    return v___x_1059_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39,
    );
    v___x_1061_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29,
    );
    v___x_1062_ = lean_array_push(v___x_1061_, v___x_1060_);
    return v___x_1062_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54,
    );
    v___x_1064_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40,
    );
    v___x_1065_ = lean_array_push(v___x_1064_, v___x_1063_);
    return v___x_1065_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41,
    );
    v___x_1067_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26;
    v___x_1068_ = crate::leanh::lean_box(2);
    v___x_1069_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    crate::leanh::lean_ctor_set(v___x_1069_, 1, v___x_1067_);
    crate::leanh::lean_ctor_set(v___x_1069_, 2, v___x_1066_);
    return v___x_1069_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42,
    );
    v___x_1071_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once),
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24,
    );
    v___x_1072_ = lean_array_push(v___x_1071_, v___x_1070_);
    return v___x_1072_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1073_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
    v___x_1074_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43,
    );
    v___x_1075_ = lean_array_push(v___x_1074_, v___x_1073_);
    return v___x_1075_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44,
    );
    v___x_1077_ = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16;
    v___x_1078_ = crate::leanh::lean_box(2);
    v___x_1079_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    crate::leanh::lean_ctor_set(v___x_1079_, 1, v___x_1077_);
    crate::leanh::lean_ctor_set(v___x_1079_, 2, v___x_1076_);
    return v___x_1079_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45,
    );
    v___x_1081_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16,
    );
    v___x_1082_ = lean_array_push(v___x_1081_, v___x_1080_);
    return v___x_1082_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46,
    );
    v___x_1084_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9;
    v___x_1085_ = crate::leanh::lean_box(2);
    v___x_1086_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1086_, 0, v___x_1085_);
    crate::leanh::lean_ctor_set(v___x_1086_, 1, v___x_1084_);
    crate::leanh::lean_ctor_set(v___x_1086_, 2, v___x_1083_);
    return v___x_1086_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47,
    );
    v___x_1088_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_1089_ = lean_array_push(v___x_1088_, v___x_1087_);
    return v___x_1089_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1090_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48,
    );
    v___x_1091_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7;
    v___x_1092_ = crate::leanh::lean_box(2);
    v___x_1093_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1093_, 0, v___x_1092_);
    crate::leanh::lean_ctor_set(v___x_1093_, 1, v___x_1091_);
    crate::leanh::lean_ctor_set(v___x_1093_, 2, v___x_1090_);
    return v___x_1093_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49,
    );
    v___x_1095_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
    v___x_1096_ = lean_array_push(v___x_1095_, v___x_1094_);
    return v___x_1096_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50,
    );
    v___x_1098_ = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4;
    v___x_1099_ = crate::leanh::lean_box(2);
    v___x_1100_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1099_);
    crate::leanh::lean_ctor_set(v___x_1100_, 1, v___x_1098_);
    crate::leanh::lean_ctor_set(v___x_1100_, 2, v___x_1097_);
    return v___x_1100_;
}
pub unsafe fn _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51),
        core::ptr::addr_of_mut!(
            l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51_once
        ),
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51,
    );
    return v___x_1101_;
}
pub unsafe fn l_Lean_Grind_CommRing_toCommSemiring___redArg(
    mut v_self_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_1103_ = crate::leanh::lean_ctor_get(v_self_1102_, 0);
    crate::leanh::lean_inc_ref(v_toSemiring_1103_);
    return v_toSemiring_1103_;
}
pub unsafe fn l_Lean_Grind_CommRing_toCommSemiring___redArg___boxed(
    mut v_self_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1105_ = l_Lean_Grind_CommRing_toCommSemiring___redArg(v_self_1104_);
    crate::leanh::lean_dec_ref(v_self_1104_);
    return v_res_1105_;
}
pub unsafe fn l_Lean_Grind_CommRing_toCommSemiring(
    mut v_00_u03b1_1106_: *mut crate::leanh::LeanObject,
    mut v_self_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_1108_ = crate::leanh::lean_ctor_get(v_self_1107_, 0);
    crate::leanh::lean_inc_ref(v_toSemiring_1108_);
    return v_toSemiring_1108_;
}
pub unsafe fn l_Lean_Grind_CommRing_toCommSemiring___boxed(
    mut v_00_u03b1_1109_: *mut crate::leanh::LeanObject,
    mut v_self_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_Lean_Grind_CommRing_toCommSemiring(v_00_u03b1_1109_, v_self_1110_);
    crate::leanh::lean_dec_ref(v_self_1110_);
    return v_res_1111_;
}
pub unsafe fn l_Lean_Grind_Semiring_toNatModule___redArg(
    mut v_I_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toAdd_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmul_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toAdd_1113_ = crate::leanh::lean_ctor_get(v_I_1112_, 0);
    crate::leanh::lean_inc(v_toAdd_1113_);
    v_ofNat_1114_ = crate::leanh::lean_ctor_get(v_I_1112_, 3);
    crate::leanh::lean_inc(v_ofNat_1114_);
    v_nsmul_1115_ = crate::leanh::lean_ctor_get(v_I_1112_, 4);
    crate::leanh::lean_inc(v_nsmul_1115_);
    crate::leanh::lean_dec_ref(v_I_1112_);
    v___x_1116_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1117_ = crate::leanh::lean_apply_1(v_ofNat_1114_, v___x_1116_);
    v___x_1118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1117_);
    crate::leanh::lean_ctor_set(v___x_1118_, 1, v_toAdd_1113_);
    v___x_1119_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1119_, 0, v___x_1118_);
    crate::leanh::lean_ctor_set(v___x_1119_, 1, v_nsmul_1115_);
    return v___x_1119_;
}
pub unsafe fn l_Lean_Grind_Semiring_toNatModule(
    mut v_00_u03b1_1120_: *mut crate::leanh::LeanObject,
    mut v_I_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = l_Lean_Grind_Semiring_toNatModule___redArg(v_I_1121_);
    return v___x_1122_;
}
pub unsafe fn l_Lean_Grind_Ring_toAddCommGroup___redArg(
    mut v_I_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toNeg_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSub_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_1124_ = crate::leanh::lean_ctor_get(v_I_1123_, 0);
    crate::leanh::lean_inc_ref(v_toSemiring_1124_);
    v_toNeg_1125_ = crate::leanh::lean_ctor_get(v_I_1123_, 1);
    crate::leanh::lean_inc(v_toNeg_1125_);
    v_toSub_1126_ = crate::leanh::lean_ctor_get(v_I_1123_, 2);
    crate::leanh::lean_inc(v_toSub_1126_);
    crate::leanh::lean_dec_ref(v_I_1123_);
    v_toAdd_1127_ = crate::leanh::lean_ctor_get(v_toSemiring_1124_, 0);
    crate::leanh::lean_inc(v_toAdd_1127_);
    v_ofNat_1128_ = crate::leanh::lean_ctor_get(v_toSemiring_1124_, 3);
    crate::leanh::lean_inc(v_ofNat_1128_);
    crate::leanh::lean_dec_ref(v_toSemiring_1124_);
    v___x_1129_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1130_ = crate::leanh::lean_apply_1(v_ofNat_1128_, v___x_1129_);
    v___x_1131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    crate::leanh::lean_ctor_set(v___x_1131_, 1, v_toAdd_1127_);
    v___x_1132_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1132_, 0, v___x_1131_);
    crate::leanh::lean_ctor_set(v___x_1132_, 1, v_toNeg_1125_);
    crate::leanh::lean_ctor_set(v___x_1132_, 2, v_toSub_1126_);
    return v___x_1132_;
}
pub unsafe fn l_Lean_Grind_Ring_toAddCommGroup(
    mut v_00_u03b1_1133_: *mut crate::leanh::LeanObject,
    mut v_I_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = l_Lean_Grind_Ring_toAddCommGroup___redArg(v_I_1134_);
    return v___x_1135_;
}
pub unsafe fn l_Lean_Grind_Ring_toIntModule___redArg(
    mut v_I_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSemiring_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toNeg_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSub_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmul_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toZero_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v_toAdd_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmul_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut v_unused_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSemiring_1137_ = crate::leanh::lean_ctor_get(v_I_1136_, 0);
                crate::leanh::lean_inc_ref_n(v_toSemiring_1137_, 2);
                v_toNeg_1138_ = crate::leanh::lean_ctor_get(v_I_1136_, 1);
                crate::leanh::lean_inc(v_toNeg_1138_);
                v_toSub_1139_ = crate::leanh::lean_ctor_get(v_I_1136_, 2);
                crate::leanh::lean_inc(v_toSub_1139_);
                v_zsmul_1140_ = crate::leanh::lean_ctor_get(v_I_1136_, 4);
                crate::leanh::lean_inc(v_zsmul_1140_);
                crate::leanh::lean_dec_ref(v_I_1136_);
                v___x_1141_ = l_Lean_Grind_Semiring_toNatModule___redArg(v_toSemiring_1137_);
                v_toAddCommMonoid_1142_ = crate::leanh::lean_ctor_get(v___x_1141_, 0);
                crate::leanh::lean_inc_ref(v_toAddCommMonoid_1142_);
                crate::leanh::lean_dec_ref(v___x_1141_);
                v_toZero_1143_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1142_, 0);
                v_isSharedCheck_1154_ =
                    (!crate::leanh::lean_is_exclusive(v_toAddCommMonoid_1142_)) as u8;
                if v_isSharedCheck_1154_ == 0 {
                    v_unused_1155_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_1142_, 1);
                    crate::leanh::lean_dec(v_unused_1155_);
                    v___x_1145_ = v_toAddCommMonoid_1142_;
                    v_isShared_1146_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toZero_1143_);
                    crate::leanh::lean_dec(v_toAddCommMonoid_1142_);
                    v___x_1145_ = crate::leanh::lean_box(0);
                    v_isShared_1146_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toAdd_1147_ = crate::leanh::lean_ctor_get(v_toSemiring_1137_, 0);
                crate::leanh::lean_inc(v_toAdd_1147_);
                v_nsmul_1148_ = crate::leanh::lean_ctor_get(v_toSemiring_1137_, 4);
                crate::leanh::lean_inc(v_nsmul_1148_);
                crate::leanh::lean_dec_ref(v_toSemiring_1137_);
                if v_isShared_1146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1145_, 1, v_toAdd_1147_);
                    v___x_1150_ = v___x_1145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1153_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_toZero_1143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_toAdd_1147_);
                    v___x_1150_ = v_reuseFailAlloc_1153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1151_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1151_, 0, v___x_1150_);
                crate::leanh::lean_ctor_set(v___x_1151_, 1, v_toNeg_1138_);
                crate::leanh::lean_ctor_set(v___x_1151_, 2, v_toSub_1139_);
                v___x_1152_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
                crate::leanh::lean_ctor_set(v___x_1152_, 1, v_nsmul_1148_);
                crate::leanh::lean_ctor_set(v___x_1152_, 2, v_zsmul_1140_);
                return v___x_1152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Ring_toIntModule(
    mut v_00_u03b1_1156_: *mut crate::leanh::LeanObject,
    mut v_I_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = l_Lean_Grind_Ring_toIntModule___redArg(v_I_1157_);
    return v___x_1158_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Module_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Ring_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Grind_Semiring_ofNat__succ___autoParam =
        _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam);
    l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam =
        _init_l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam);
    l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam =
        _init_l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam);
    l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam =
        _init_l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam);
    l_Lean_Grind_Ring_intCast__ofNat___autoParam =
        _init_l_Lean_Grind_Ring_intCast__ofNat___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Ring_intCast__ofNat___autoParam);
    l_Lean_Grind_Ring_intCast__neg___autoParam = _init_l_Lean_Grind_Ring_intCast__neg___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_Ring_intCast__neg___autoParam);
    l_Lean_Grind_CommSemiring_one__mul___autoParam =
        _init_l_Lean_Grind_CommSemiring_one__mul___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam);
    l_Lean_Grind_CommSemiring_mul__zero___autoParam =
        _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam);
    l_Lean_Grind_CommSemiring_right__distrib___autoParam =
        _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Ring_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Module_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Ring_Basic(builtin);
}
