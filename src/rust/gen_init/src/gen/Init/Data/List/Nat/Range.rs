// Lean compiler output
// Module: Init.Data.List.Nat.Range
// Imports: Init.Data.Nat.Lemmas Init.Ext Init.ByCases Init.Data.List.Erase Init.Data.List.Find Init.Data.List.Nat.TakeDrop Init.Data.List.Pairwise Init.Data.List.Range Init.Data.List.Zip Init.Data.Nat.Dvd Init.Data.Option.Lemmas Init.Omega Init.TacticsExtra
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::List::Erase::{
    initialize_Init_Data_List_Erase, runtime_initialize_Init_Data_List_Erase,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::List::Zip::{
    initialize_Init_Data_List_Zip, runtime_initialize_Init_Data_List_Zip,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::ffi::lean_array_push;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__0_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__1_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__2_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__3_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_List_pairwise__lt__range_x27___auto__1___closed__4_value:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_List_pairwise__lt__range_x27___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__5_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__6_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_List_pairwise__lt__range_x27___auto__1___closed__7_value:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_List_pairwise__lt__range_x27___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__8_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__9_value:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_List_pairwise__lt__range_x27___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__10_value:
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
    m_data: [115, 105, 109, 112, 0],
};
static mut l_List_pairwise__lt__range_x27___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_List_pairwise__lt__range_x27___auto__1___closed__11_value:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        12783917532758215986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_List_pairwise__lt__range_x27___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_pairwise__lt__range_x27___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_pairwise__lt__range_x27___auto__1___closed__14_value:
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
static mut l_List_pairwise__lt__range_x27___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_1:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_2:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_List_pairwise__lt__range_x27___auto__1___closed__15_value:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_List_pairwise__lt__range_x27___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_pairwise__lt__range_x27___auto__1___closed__16_value:
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
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_List_pairwise__lt__range_x27___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_pairwise__lt__range_x27___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_pairwise__lt__range_x27___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_pairwise__lt__range_x27___auto__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_pairwise__lt__range_x27___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_List_pairwise__lt__range_x27___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_List_nodup__range_x27___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_List_count__range_x27___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_118_ = l_List_pairwise__lt__range_x27___auto__1___closed__10;
    v___x_119_ = l_Lean_mkAtom(v___x_118_);
    return v___x_119_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__12_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__12,
    );
    v___x_121_ = l_List_pairwise__lt__range_x27___auto__1___closed__5;
    v___x_122_ = lean_array_push(v___x_121_, v___x_120_);
    return v___x_122_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_133_ = l_List_pairwise__lt__range_x27___auto__1___closed__16;
    v___x_134_ = l_List_pairwise__lt__range_x27___auto__1___closed__5;
    v___x_135_ = lean_array_push(v___x_134_, v___x_133_);
    return v___x_135_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__17_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__17,
    );
    v___x_137_ = l_List_pairwise__lt__range_x27___auto__1___closed__15;
    v___x_138_ = crate::leanh::lean_box(2);
    v___x_139_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_139_, 0, v___x_138_);
    crate::leanh::lean_ctor_set(v___x_139_, 1, v___x_137_);
    crate::leanh::lean_ctor_set(v___x_139_, 2, v___x_136_);
    return v___x_139_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__18_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__18,
    );
    v___x_141_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__13_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__13,
    );
    v___x_142_ = lean_array_push(v___x_141_, v___x_140_);
    return v___x_142_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_143_ = l_List_pairwise__lt__range_x27___auto__1___closed__16;
    v___x_144_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__19_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__19,
    );
    v___x_145_ = lean_array_push(v___x_144_, v___x_143_);
    return v___x_145_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_146_ = l_List_pairwise__lt__range_x27___auto__1___closed__16;
    v___x_147_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__20_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__20,
    );
    v___x_148_ = lean_array_push(v___x_147_, v___x_146_);
    return v___x_148_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = l_List_pairwise__lt__range_x27___auto__1___closed__16;
    v___x_150_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__21_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__21,
    );
    v___x_151_ = lean_array_push(v___x_150_, v___x_149_);
    return v___x_151_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = l_List_pairwise__lt__range_x27___auto__1___closed__16;
    v___x_153_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__22_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__22,
    );
    v___x_154_ = lean_array_push(v___x_153_, v___x_152_);
    return v___x_154_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_155_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__23_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__23,
    );
    v___x_156_ = l_List_pairwise__lt__range_x27___auto__1___closed__11;
    v___x_157_ = crate::leanh::lean_box(2);
    v___x_158_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_158_, 0, v___x_157_);
    crate::leanh::lean_ctor_set(v___x_158_, 1, v___x_156_);
    crate::leanh::lean_ctor_set(v___x_158_, 2, v___x_155_);
    return v___x_158_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_159_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__24_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__24,
    );
    v___x_160_ = l_List_pairwise__lt__range_x27___auto__1___closed__5;
    v___x_161_ = lean_array_push(v___x_160_, v___x_159_);
    return v___x_161_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_162_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__25_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__25,
    );
    v___x_163_ = l_List_pairwise__lt__range_x27___auto__1___closed__9;
    v___x_164_ = crate::leanh::lean_box(2);
    v___x_165_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_165_, 0, v___x_164_);
    crate::leanh::lean_ctor_set(v___x_165_, 1, v___x_163_);
    crate::leanh::lean_ctor_set(v___x_165_, 2, v___x_162_);
    return v___x_165_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__26_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__26,
    );
    v___x_167_ = l_List_pairwise__lt__range_x27___auto__1___closed__5;
    v___x_168_ = lean_array_push(v___x_167_, v___x_166_);
    return v___x_168_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_169_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__27_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__27,
    );
    v___x_170_ = l_List_pairwise__lt__range_x27___auto__1___closed__7;
    v___x_171_ = crate::leanh::lean_box(2);
    v___x_172_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_172_, 0, v___x_171_);
    crate::leanh::lean_ctor_set(v___x_172_, 1, v___x_170_);
    crate::leanh::lean_ctor_set(v___x_172_, 2, v___x_169_);
    return v___x_172_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_173_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__28_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__28,
    );
    v___x_174_ = l_List_pairwise__lt__range_x27___auto__1___closed__5;
    v___x_175_ = lean_array_push(v___x_174_, v___x_173_);
    return v___x_175_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_176_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__29_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__29,
    );
    v___x_177_ = l_List_pairwise__lt__range_x27___auto__1___closed__4;
    v___x_178_ = crate::leanh::lean_box(2);
    v___x_179_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_179_, 0, v___x_178_);
    crate::leanh::lean_ctor_set(v___x_179_, 1, v___x_177_);
    crate::leanh::lean_ctor_set(v___x_179_, 2, v___x_176_);
    return v___x_179_;
}
pub unsafe fn _init_l_List_pairwise__lt__range_x27___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_180_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__30_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__30,
    );
    return v___x_180_;
}
pub unsafe fn _init_l_List_nodup__range_x27___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_181_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__30_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__30,
    );
    return v___x_181_;
}
pub unsafe fn _init_l_List_count__range_x27___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_List_pairwise__lt__range_x27___auto__1___closed__30_once),
        _init_l_List_pairwise__lt__range_x27___auto__1___closed__30,
    );
    return v___x_182_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Nat_Range(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Nat_Range(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_pairwise__lt__range_x27___auto__1 = _init_l_List_pairwise__lt__range_x27___auto__1();
    crate::leanh::lean_mark_persistent(l_List_pairwise__lt__range_x27___auto__1);
    l_List_nodup__range_x27___auto__1 = _init_l_List_nodup__range_x27___auto__1();
    crate::leanh::lean_mark_persistent(l_List_nodup__range_x27___auto__1);
    l_List_count__range_x27___auto__1 = _init_l_List_count__range_x27___auto__1();
    crate::leanh::lean_mark_persistent(l_List_count__range_x27___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Nat_Range(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Nat_Range(builtin);
}
