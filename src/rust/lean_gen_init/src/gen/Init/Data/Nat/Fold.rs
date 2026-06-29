// Lean compiler output
// Module: Init.Data.Nat.Fold
// Imports: Init.Data.List.FinRange Init.Data.Fin.Lemmas Init.Data.List.Lemmas Init.Omega
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::List::FinRange::{
    initialize_Init_Data_List_FinRange, runtime_initialize_Init_Data_List_FinRange,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value:
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
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value:
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
    m_data: [111, 109, 101, 103, 97, 0],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        14893461734720614794 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value:
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16_value:
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
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfoldRev___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold__zero___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold__succ___auto__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold__congr___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold__add___auto__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__zero___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__succ___auto__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__congr___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__add___auto__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Nat_fold___redArg___lam__0(
    mut v_x_642_: *mut crate::leanh::LeanObject,
    mut v_i_643_: *mut crate::leanh::LeanObject,
    mut v_h_644_: *mut crate::leanh::LeanObject,
    mut v___y_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ =
        crate::leanh::lean_apply_3(v_x_642_, v_i_643_, crate::leanh::lean_box(0), v___y_645_);
    return v___x_646_;
}
pub unsafe fn l_Nat_fold___redArg(
    mut v_x_647_: *mut crate::leanh::LeanObject,
    mut v_x_648_: *mut crate::leanh::LeanObject,
    mut v_x_649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_651_: u8 = 0;
    v_zero_650_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_651_ = lean_nat_dec_eq(v_x_647_, v_zero_650_);
    if v_isZero_651_ == 1 {
        crate::leanh::lean_dec(v_x_648_);
        crate::leanh::lean_inc(v_x_649_);
        return v_x_649_;
    } else {
        let mut v___f_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_x_648_);
        v___f_652_ = crate::leanh::lean_alloc_closure(
            l_Nat_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_652_, 0, v_x_648_);
        v_one_653_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_654_ = lean_nat_sub(v_x_647_, v_one_653_);
        v___x_655_ = l_Nat_fold___redArg(v_n_654_, v___f_652_, v_x_649_);
        v___x_656_ =
            crate::leanh::lean_apply_3(v_x_648_, v_n_654_, crate::leanh::lean_box(0), v___x_655_);
        return v___x_656_;
    }
}
pub unsafe fn l_Nat_fold___redArg___boxed(
    mut v_x_657_: *mut crate::leanh::LeanObject,
    mut v_x_658_: *mut crate::leanh::LeanObject,
    mut v_x_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Nat_fold___redArg(v_x_657_, v_x_658_, v_x_659_);
    crate::leanh::lean_dec(v_x_659_);
    crate::leanh::lean_dec(v_x_657_);
    return v_res_660_;
}
pub unsafe fn l_Nat_fold(
    mut v_00_u03b1_661_: *mut crate::leanh::LeanObject,
    mut v_x_662_: *mut crate::leanh::LeanObject,
    mut v_x_663_: *mut crate::leanh::LeanObject,
    mut v_x_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Nat_fold___redArg(v_x_662_, v_x_663_, v_x_664_);
    return v___x_665_;
}
pub unsafe fn l_Nat_fold___boxed(
    mut v_00_u03b1_666_: *mut crate::leanh::LeanObject,
    mut v_x_667_: *mut crate::leanh::LeanObject,
    mut v_x_668_: *mut crate::leanh::LeanObject,
    mut v_x_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Nat_fold(v_00_u03b1_666_, v_x_667_, v_x_668_, v_x_669_);
    crate::leanh::lean_dec(v_x_669_);
    crate::leanh::lean_dec(v_x_667_);
    return v_res_670_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
    mut v_n_671_: *mut crate::leanh::LeanObject,
    mut v_f_672_: *mut crate::leanh::LeanObject,
    mut v_j_673_: *mut crate::leanh::LeanObject,
    mut v_a_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_676_: u8 = 0;
    let mut v_one_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_675_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_676_ = lean_nat_dec_eq(v_j_673_, v_zero_675_);
                if v_isZero_676_ == 1 {
                    crate::leanh::lean_dec(v_j_673_);
                    crate::leanh::lean_dec(v_f_672_);
                    return v_a_674_;
                } else {
                    v_one_677_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_678_ = lean_nat_sub(v_j_673_, v_one_677_);
                    v___x_679_ = lean_nat_sub(v_n_671_, v_j_673_);
                    crate::leanh::lean_dec(v_j_673_);
                    crate::leanh::lean_inc(v_f_672_);
                    v___x_680_ = crate::leanh::lean_apply_3(
                        v_f_672_,
                        v___x_679_,
                        crate::leanh::lean_box(0),
                        v_a_674_,
                    );
                    v_j_673_ = v_n_678_;
                    v_a_674_ = v___x_680_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg___boxed(
    mut v_n_682_: *mut crate::leanh::LeanObject,
    mut v_f_683_: *mut crate::leanh::LeanObject,
    mut v_j_684_: *mut crate::leanh::LeanObject,
    mut v_a_685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_686_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_682_, v_f_683_, v_j_684_, v_a_685_,
    );
    crate::leanh::lean_dec(v_n_682_);
    return v_res_686_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(
    mut v_00_u03b1_687_: *mut crate::leanh::LeanObject,
    mut v_n_688_: *mut crate::leanh::LeanObject,
    mut v_f_689_: *mut crate::leanh::LeanObject,
    mut v_j_690_: *mut crate::leanh::LeanObject,
    mut v_a_691_: *mut crate::leanh::LeanObject,
    mut v_a_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_688_, v_f_689_, v_j_690_, v_a_692_,
    );
    return v___x_693_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___boxed(
    mut v_00_u03b1_694_: *mut crate::leanh::LeanObject,
    mut v_n_695_: *mut crate::leanh::LeanObject,
    mut v_f_696_: *mut crate::leanh::LeanObject,
    mut v_j_697_: *mut crate::leanh::LeanObject,
    mut v_a_698_: *mut crate::leanh::LeanObject,
    mut v_a_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_700_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(
        v_00_u03b1_694_,
        v_n_695_,
        v_f_696_,
        v_j_697_,
        v_a_698_,
        v_a_699_,
    );
    crate::leanh::lean_dec(v_n_695_);
    return v_res_700_;
}
pub unsafe fn l_Nat_foldTR___redArg(
    mut v_n_701_: *mut crate::leanh::LeanObject,
    mut v_f_702_: *mut crate::leanh::LeanObject,
    mut v_init_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_701_);
    v___x_704_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_701_,
        v_f_702_,
        v_n_701_,
        v_init_703_,
    );
    crate::leanh::lean_dec(v_n_701_);
    return v___x_704_;
}
pub unsafe fn l_Nat_foldTR(
    mut v_00_u03b1_705_: *mut crate::leanh::LeanObject,
    mut v_n_706_: *mut crate::leanh::LeanObject,
    mut v_f_707_: *mut crate::leanh::LeanObject,
    mut v_init_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_706_);
    v___x_709_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_706_,
        v_f_707_,
        v_n_706_,
        v_init_708_,
    );
    crate::leanh::lean_dec(v_n_706_);
    return v___x_709_;
}
pub unsafe fn l_Nat_foldRev___redArg(
    mut v_x_710_: *mut crate::leanh::LeanObject,
    mut v_x_711_: *mut crate::leanh::LeanObject,
    mut v_x_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_714_: u8 = 0;
    let mut v___f_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_713_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_714_ = lean_nat_dec_eq(v_x_710_, v_zero_713_);
                if v_isZero_714_ == 1 {
                    crate::leanh::lean_dec(v_x_711_);
                    crate::leanh::lean_dec(v_x_710_);
                    return v_x_712_;
                } else {
                    crate::leanh::lean_inc(v_x_711_);
                    v___f_715_ = crate::leanh::lean_alloc_closure(
                        l_Nat_fold___redArg___lam__0 as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_715_, 0, v_x_711_);
                    v_one_716_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_717_ = lean_nat_sub(v_x_710_, v_one_716_);
                    crate::leanh::lean_dec(v_x_710_);
                    crate::leanh::lean_inc(v_n_717_);
                    v___x_718_ = crate::leanh::lean_apply_3(
                        v_x_711_,
                        v_n_717_,
                        crate::leanh::lean_box(0),
                        v_x_712_,
                    );
                    v_x_710_ = v_n_717_;
                    v_x_711_ = v___f_715_;
                    v_x_712_ = v___x_718_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_foldRev(
    mut v_00_u03b1_720_: *mut crate::leanh::LeanObject,
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_x_722_: *mut crate::leanh::LeanObject,
    mut v_x_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Nat_foldRev___redArg(v_x_721_, v_x_722_, v_x_723_);
    return v___x_724_;
}
pub unsafe fn l_Nat_any___lam__0(
    mut v_x_725_: *mut crate::leanh::LeanObject,
    mut v_i_726_: *mut crate::leanh::LeanObject,
    mut v_h_727_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: u8 = 0;
    v___x_728_ = crate::leanh::lean_apply_2(v_x_725_, v_i_726_, crate::leanh::lean_box(0));
    v___x_729_ = (crate::leanh::lean_unbox(v___x_728_) as u8);
    return v___x_729_;
}
pub unsafe fn l_Nat_any___lam__0___boxed(
    mut v_x_730_: *mut crate::leanh::LeanObject,
    mut v_i_731_: *mut crate::leanh::LeanObject,
    mut v_h_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_733_: u8 = 0;
    let mut v_r_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Nat_any___lam__0(v_x_730_, v_i_731_, v_h_732_);
    v_r_734_ = crate::leanh::lean_box((v_res_733_) as usize);
    return v_r_734_;
}
pub unsafe fn l_Nat_any(
    mut v_x_735_: *mut crate::leanh::LeanObject,
    mut v_x_736_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_738_: u8 = 0;
    v_zero_737_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_738_ = lean_nat_dec_eq(v_x_735_, v_zero_737_);
    if v_isZero_738_ == 1 {
        let mut v___x_739_: u8 = 0;
        crate::leanh::lean_dec_ref(v_x_736_);
        v___x_739_ = 0;
        return v___x_739_;
    } else {
        let mut v___f_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_743_: u8 = 0;
        crate::leanh::lean_inc_ref(v_x_736_);
        v___f_740_ = crate::leanh::lean_alloc_closure(
            l_Nat_any___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_740_, 0, v_x_736_);
        v_one_741_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_742_ = lean_nat_sub(v_x_735_, v_one_741_);
        v___x_743_ = l_Nat_any(v_n_742_, v___f_740_);
        if v___x_743_ == 0 {
            let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_745_: u8 = 0;
            v___x_744_ = crate::leanh::lean_apply_2(v_x_736_, v_n_742_, crate::leanh::lean_box(0));
            v___x_745_ = (crate::leanh::lean_unbox(v___x_744_) as u8);
            return v___x_745_;
        } else {
            crate::leanh::lean_dec(v_n_742_);
            crate::leanh::lean_dec_ref(v_x_736_);
            return v___x_743_;
        }
    }
}
pub unsafe fn l_Nat_any___boxed(
    mut v_x_746_: *mut crate::leanh::LeanObject,
    mut v_x_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: u8 = 0;
    let mut v_r_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Nat_any(v_x_746_, v_x_747_);
    crate::leanh::lean_dec(v_x_746_);
    v_r_749_ = crate::leanh::lean_box((v_res_748_) as usize);
    return v_r_749_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(
    mut v_n_750_: *mut crate::leanh::LeanObject,
    mut v_f_751_: *mut crate::leanh::LeanObject,
    mut v_i_752_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_754_: u8 = 0;
    let mut v___x_755_: u8 = 0;
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    let mut v_one_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_753_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_754_ = lean_nat_dec_eq(v_i_752_, v_zero_753_);
                if v_isZero_754_ == 1 {
                    crate::leanh::lean_dec(v_i_752_);
                    crate::leanh::lean_dec_ref(v_f_751_);
                    v___x_755_ = 0;
                    return v___x_755_;
                } else {
                    v___x_756_ = lean_nat_sub(v_n_750_, v_i_752_);
                    crate::leanh::lean_inc_ref(v_f_751_);
                    v___x_757_ =
                        crate::leanh::lean_apply_2(v_f_751_, v___x_756_, crate::leanh::lean_box(0));
                    v___x_758_ = (crate::leanh::lean_unbox(v___x_757_) as u8);
                    if v___x_758_ == 0 {
                        v_one_759_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_760_ = lean_nat_sub(v_i_752_, v_one_759_);
                        crate::leanh::lean_dec(v_i_752_);
                        v_i_752_ = v_n_760_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_752_);
                        crate::leanh::lean_dec_ref(v_f_751_);
                        v___x_762_ = (crate::leanh::lean_unbox(v___x_757_) as u8);
                        return v___x_762_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg___boxed(
    mut v_n_763_: *mut crate::leanh::LeanObject,
    mut v_f_764_: *mut crate::leanh::LeanObject,
    mut v_i_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_766_: u8 = 0;
    let mut v_r_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_763_, v_f_764_, v_i_765_);
    crate::leanh::lean_dec(v_n_763_);
    v_r_767_ = crate::leanh::lean_box((v_res_766_) as usize);
    return v_r_767_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(
    mut v_n_768_: *mut crate::leanh::LeanObject,
    mut v_f_769_: *mut crate::leanh::LeanObject,
    mut v_i_770_: *mut crate::leanh::LeanObject,
    mut v_a_771_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_772_: u8 = 0;
    v___x_772_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_768_, v_f_769_, v_i_770_);
    return v___x_772_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___boxed(
    mut v_n_773_: *mut crate::leanh::LeanObject,
    mut v_f_774_: *mut crate::leanh::LeanObject,
    mut v_i_775_: *mut crate::leanh::LeanObject,
    mut v_a_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_777_: u8 = 0;
    let mut v_r_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(v_n_773_, v_f_774_, v_i_775_, v_a_776_);
    crate::leanh::lean_dec(v_n_773_);
    v_r_778_ = crate::leanh::lean_box((v_res_777_) as usize);
    return v_r_778_;
}
pub unsafe fn l_Nat_anyTR(
    mut v_n_779_: *mut crate::leanh::LeanObject,
    mut v_f_780_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_781_: u8 = 0;
    crate::leanh::lean_inc(v_n_779_);
    v___x_781_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_779_, v_f_780_, v_n_779_);
    crate::leanh::lean_dec(v_n_779_);
    return v___x_781_;
}
pub unsafe fn l_Nat_anyTR___boxed(
    mut v_n_782_: *mut crate::leanh::LeanObject,
    mut v_f_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: u8 = 0;
    let mut v_r_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Nat_anyTR(v_n_782_, v_f_783_);
    v_r_785_ = crate::leanh::lean_box((v_res_784_) as usize);
    return v_r_785_;
}
pub unsafe fn l_Nat_all(
    mut v_x_786_: *mut crate::leanh::LeanObject,
    mut v_x_787_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_789_: u8 = 0;
    v_zero_788_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_789_ = lean_nat_dec_eq(v_x_786_, v_zero_788_);
    if v_isZero_789_ == 1 {
        crate::leanh::lean_dec_ref(v_x_787_);
        return v_isZero_789_;
    } else {
        let mut v___f_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_793_: u8 = 0;
        crate::leanh::lean_inc_ref(v_x_787_);
        v___f_790_ = crate::leanh::lean_alloc_closure(
            l_Nat_any___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_790_, 0, v_x_787_);
        v_one_791_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_792_ = lean_nat_sub(v_x_786_, v_one_791_);
        v___x_793_ = l_Nat_all(v_n_792_, v___f_790_);
        if v___x_793_ == 0 {
            crate::leanh::lean_dec(v_n_792_);
            crate::leanh::lean_dec_ref(v_x_787_);
            return v___x_793_;
        } else {
            let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_795_: u8 = 0;
            v___x_794_ = crate::leanh::lean_apply_2(v_x_787_, v_n_792_, crate::leanh::lean_box(0));
            v___x_795_ = (crate::leanh::lean_unbox(v___x_794_) as u8);
            return v___x_795_;
        }
    }
}
pub unsafe fn l_Nat_all___boxed(
    mut v_x_796_: *mut crate::leanh::LeanObject,
    mut v_x_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: u8 = 0;
    let mut v_r_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Nat_all(v_x_796_, v_x_797_);
    crate::leanh::lean_dec(v_x_796_);
    v_r_799_ = crate::leanh::lean_box((v_res_798_) as usize);
    return v_r_799_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(
    mut v_n_800_: *mut crate::leanh::LeanObject,
    mut v_f_801_: *mut crate::leanh::LeanObject,
    mut v_i_802_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_804_: u8 = 0;
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: u8 = 0;
    let mut v_one_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_803_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_804_ = lean_nat_dec_eq(v_i_802_, v_zero_803_);
                if v_isZero_804_ == 1 {
                    crate::leanh::lean_dec(v_i_802_);
                    crate::leanh::lean_dec_ref(v_f_801_);
                    return v_isZero_804_;
                } else {
                    v___x_805_ = lean_nat_sub(v_n_800_, v_i_802_);
                    crate::leanh::lean_inc_ref(v_f_801_);
                    v___x_806_ =
                        crate::leanh::lean_apply_2(v_f_801_, v___x_805_, crate::leanh::lean_box(0));
                    v___x_807_ = (crate::leanh::lean_unbox(v___x_806_) as u8);
                    if v___x_807_ == 0 {
                        crate::leanh::lean_dec(v_i_802_);
                        crate::leanh::lean_dec_ref(v_f_801_);
                        v___x_808_ = (crate::leanh::lean_unbox(v___x_806_) as u8);
                        return v___x_808_;
                    } else {
                        v_one_809_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_810_ = lean_nat_sub(v_i_802_, v_one_809_);
                        crate::leanh::lean_dec(v_i_802_);
                        v_i_802_ = v_n_810_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg___boxed(
    mut v_n_812_: *mut crate::leanh::LeanObject,
    mut v_f_813_: *mut crate::leanh::LeanObject,
    mut v_i_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_815_: u8 = 0;
    let mut v_r_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_815_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_812_, v_f_813_, v_i_814_);
    crate::leanh::lean_dec(v_n_812_);
    v_r_816_ = crate::leanh::lean_box((v_res_815_) as usize);
    return v_r_816_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(
    mut v_n_817_: *mut crate::leanh::LeanObject,
    mut v_f_818_: *mut crate::leanh::LeanObject,
    mut v_i_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_821_: u8 = 0;
    v___x_821_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_817_, v_f_818_, v_i_819_);
    return v___x_821_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___boxed(
    mut v_n_822_: *mut crate::leanh::LeanObject,
    mut v_f_823_: *mut crate::leanh::LeanObject,
    mut v_i_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_826_: u8 = 0;
    let mut v_r_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_826_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(v_n_822_, v_f_823_, v_i_824_, v_a_825_);
    crate::leanh::lean_dec(v_n_822_);
    v_r_827_ = crate::leanh::lean_box((v_res_826_) as usize);
    return v_r_827_;
}
pub unsafe fn l_Nat_allTR(
    mut v_n_828_: *mut crate::leanh::LeanObject,
    mut v_f_829_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_830_: u8 = 0;
    crate::leanh::lean_inc(v_n_828_);
    v___x_830_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_828_, v_f_829_, v_n_828_);
    crate::leanh::lean_dec(v_n_828_);
    return v___x_830_;
}
pub unsafe fn l_Nat_allTR___boxed(
    mut v_n_831_: *mut crate::leanh::LeanObject,
    mut v_f_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_833_: u8 = 0;
    let mut v_r_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_833_ = l_Nat_allTR(v_n_831_, v_f_832_);
    v_r_834_ = crate::leanh::lean_box((v_res_833_) as usize);
    return v_r_834_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(
    mut v_x_835_: *mut crate::leanh::LeanObject,
    mut v_x_836_: *mut crate::leanh::LeanObject,
    mut v_h__1_837_: *mut crate::leanh::LeanObject,
    mut v_h__2_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_840_: u8 = 0;
    v_zero_839_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_840_ = lean_nat_dec_eq(v_x_835_, v_zero_839_);
    if v_isZero_840_ == 1 {
        let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_838_);
        v___x_841_ = crate::leanh::lean_apply_2(v_h__1_837_, crate::leanh::lean_box(0), v_x_836_);
        return v___x_841_;
    } else {
        let mut v_one_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_837_);
        v_one_842_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_843_ = lean_nat_sub(v_x_835_, v_one_842_);
        v___x_844_ =
            crate::leanh::lean_apply_3(v_h__2_838_, v_n_843_, crate::leanh::lean_box(0), v_x_836_);
        return v___x_844_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg___boxed(
    mut v_x_845_: *mut crate::leanh::LeanObject,
    mut v_x_846_: *mut crate::leanh::LeanObject,
    mut v_h__1_847_: *mut crate::leanh::LeanObject,
    mut v_h__2_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_849_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(
        v_x_845_,
        v_x_846_,
        v_h__1_847_,
        v_h__2_848_,
    );
    crate::leanh::lean_dec(v_x_845_);
    return v_res_849_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(
    mut v_00_u03b1_850_: *mut crate::leanh::LeanObject,
    mut v_n_851_: *mut crate::leanh::LeanObject,
    mut v_motive_852_: *mut crate::leanh::LeanObject,
    mut v_x_853_: *mut crate::leanh::LeanObject,
    mut v_x_854_: *mut crate::leanh::LeanObject,
    mut v_x_855_: *mut crate::leanh::LeanObject,
    mut v_h__1_856_: *mut crate::leanh::LeanObject,
    mut v_h__2_857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_859_: u8 = 0;
    v_zero_858_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_859_ = lean_nat_dec_eq(v_x_853_, v_zero_858_);
    if v_isZero_859_ == 1 {
        let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_857_);
        v___x_860_ = crate::leanh::lean_apply_2(v_h__1_856_, crate::leanh::lean_box(0), v_x_855_);
        return v___x_860_;
    } else {
        let mut v_one_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_856_);
        v_one_861_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_862_ = lean_nat_sub(v_x_853_, v_one_861_);
        v___x_863_ =
            crate::leanh::lean_apply_3(v_h__2_857_, v_n_862_, crate::leanh::lean_box(0), v_x_855_);
        return v___x_863_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___boxed(
    mut v_00_u03b1_864_: *mut crate::leanh::LeanObject,
    mut v_n_865_: *mut crate::leanh::LeanObject,
    mut v_motive_866_: *mut crate::leanh::LeanObject,
    mut v_x_867_: *mut crate::leanh::LeanObject,
    mut v_x_868_: *mut crate::leanh::LeanObject,
    mut v_x_869_: *mut crate::leanh::LeanObject,
    mut v_h__1_870_: *mut crate::leanh::LeanObject,
    mut v_h__2_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_872_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(
        v_00_u03b1_864_,
        v_n_865_,
        v_motive_866_,
        v_x_867_,
        v_x_868_,
        v_x_869_,
        v_h__1_870_,
        v_h__2_871_,
    );
    crate::leanh::lean_dec(v_x_867_);
    crate::leanh::lean_dec(v_n_865_);
    return v_res_872_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(
    mut v_x_873_: *mut crate::leanh::LeanObject,
    mut v_x_874_: *mut crate::leanh::LeanObject,
    mut v_x_875_: *mut crate::leanh::LeanObject,
    mut v_h__1_876_: *mut crate::leanh::LeanObject,
    mut v_h__2_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_879_: u8 = 0;
    v_zero_878_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_879_ = lean_nat_dec_eq(v_x_873_, v_zero_878_);
    if v_isZero_879_ == 1 {
        let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_877_);
        v___x_880_ = crate::leanh::lean_apply_2(v_h__1_876_, v_x_874_, v_x_875_);
        return v___x_880_;
    } else {
        let mut v_one_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_876_);
        v_one_881_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_882_ = lean_nat_sub(v_x_873_, v_one_881_);
        v___x_883_ = crate::leanh::lean_apply_3(v_h__2_877_, v_n_882_, v_x_874_, v_x_875_);
        return v___x_883_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg___boxed(
    mut v_x_884_: *mut crate::leanh::LeanObject,
    mut v_x_885_: *mut crate::leanh::LeanObject,
    mut v_x_886_: *mut crate::leanh::LeanObject,
    mut v_h__1_887_: *mut crate::leanh::LeanObject,
    mut v_h__2_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_889_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(
        v_x_884_,
        v_x_885_,
        v_x_886_,
        v_h__1_887_,
        v_h__2_888_,
    );
    crate::leanh::lean_dec(v_x_884_);
    return v_res_889_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(
    mut v_00_u03b1_890_: *mut crate::leanh::LeanObject,
    mut v_motive_891_: *mut crate::leanh::LeanObject,
    mut v_x_892_: *mut crate::leanh::LeanObject,
    mut v_x_893_: *mut crate::leanh::LeanObject,
    mut v_x_894_: *mut crate::leanh::LeanObject,
    mut v_h__1_895_: *mut crate::leanh::LeanObject,
    mut v_h__2_896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_898_: u8 = 0;
    v_zero_897_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_898_ = lean_nat_dec_eq(v_x_892_, v_zero_897_);
    if v_isZero_898_ == 1 {
        let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_896_);
        v___x_899_ = crate::leanh::lean_apply_2(v_h__1_895_, v_x_893_, v_x_894_);
        return v___x_899_;
    } else {
        let mut v_one_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_895_);
        v_one_900_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_901_ = lean_nat_sub(v_x_892_, v_one_900_);
        v___x_902_ = crate::leanh::lean_apply_3(v_h__2_896_, v_n_901_, v_x_893_, v_x_894_);
        return v___x_902_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___boxed(
    mut v_00_u03b1_903_: *mut crate::leanh::LeanObject,
    mut v_motive_904_: *mut crate::leanh::LeanObject,
    mut v_x_905_: *mut crate::leanh::LeanObject,
    mut v_x_906_: *mut crate::leanh::LeanObject,
    mut v_x_907_: *mut crate::leanh::LeanObject,
    mut v_h__1_908_: *mut crate::leanh::LeanObject,
    mut v_h__2_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(
        v_00_u03b1_903_,
        v_motive_904_,
        v_x_905_,
        v_x_906_,
        v_x_907_,
        v_h__1_908_,
        v_h__2_909_,
    );
    crate::leanh::lean_dec(v_x_905_);
    return v_res_910_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(
    mut v_x_911_: *mut crate::leanh::LeanObject,
    mut v_h__1_912_: *mut crate::leanh::LeanObject,
    mut v_h__2_913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_915_: u8 = 0;
    v_zero_914_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_915_ = lean_nat_dec_eq(v_x_911_, v_zero_914_);
    if v_isZero_915_ == 1 {
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_913_);
        v___x_916_ = crate::leanh::lean_apply_1(v_h__1_912_, crate::leanh::lean_box(0));
        return v___x_916_;
    } else {
        let mut v_one_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_912_);
        v_one_917_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_918_ = lean_nat_sub(v_x_911_, v_one_917_);
        v___x_919_ = crate::leanh::lean_apply_2(v_h__2_913_, v_n_918_, crate::leanh::lean_box(0));
        return v___x_919_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg___boxed(
    mut v_x_920_: *mut crate::leanh::LeanObject,
    mut v_h__1_921_: *mut crate::leanh::LeanObject,
    mut v_h__2_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_923_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(
        v_x_920_,
        v_h__1_921_,
        v_h__2_922_,
    );
    crate::leanh::lean_dec(v_x_920_);
    return v_res_923_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(
    mut v_n_924_: *mut crate::leanh::LeanObject,
    mut v_motive_925_: *mut crate::leanh::LeanObject,
    mut v_x_926_: *mut crate::leanh::LeanObject,
    mut v_x_927_: *mut crate::leanh::LeanObject,
    mut v_h__1_928_: *mut crate::leanh::LeanObject,
    mut v_h__2_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_931_: u8 = 0;
    v_zero_930_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_931_ = lean_nat_dec_eq(v_x_926_, v_zero_930_);
    if v_isZero_931_ == 1 {
        let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_929_);
        v___x_932_ = crate::leanh::lean_apply_1(v_h__1_928_, crate::leanh::lean_box(0));
        return v___x_932_;
    } else {
        let mut v_one_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_928_);
        v_one_933_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_934_ = lean_nat_sub(v_x_926_, v_one_933_);
        v___x_935_ = crate::leanh::lean_apply_2(v_h__2_929_, v_n_934_, crate::leanh::lean_box(0));
        return v___x_935_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___boxed(
    mut v_n_936_: *mut crate::leanh::LeanObject,
    mut v_motive_937_: *mut crate::leanh::LeanObject,
    mut v_x_938_: *mut crate::leanh::LeanObject,
    mut v_x_939_: *mut crate::leanh::LeanObject,
    mut v_h__1_940_: *mut crate::leanh::LeanObject,
    mut v_h__2_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_942_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(
        v_n_936_,
        v_motive_937_,
        v_x_938_,
        v_x_939_,
        v_h__1_940_,
        v_h__2_941_,
    );
    crate::leanh::lean_dec(v_x_938_);
    crate::leanh::lean_dec(v_n_936_);
    return v_res_942_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(
    mut v_x_943_: *mut crate::leanh::LeanObject,
    mut v_x_944_: *mut crate::leanh::LeanObject,
    mut v_h__1_945_: *mut crate::leanh::LeanObject,
    mut v_h__2_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_948_: u8 = 0;
    v_zero_947_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_948_ = lean_nat_dec_eq(v_x_943_, v_zero_947_);
    if v_isZero_948_ == 1 {
        let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_946_);
        v___x_949_ = crate::leanh::lean_apply_1(v_h__1_945_, v_x_944_);
        return v___x_949_;
    } else {
        let mut v_one_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_945_);
        v_one_950_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_951_ = lean_nat_sub(v_x_943_, v_one_950_);
        v___x_952_ = crate::leanh::lean_apply_2(v_h__2_946_, v_n_951_, v_x_944_);
        return v___x_952_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg___boxed(
    mut v_x_953_: *mut crate::leanh::LeanObject,
    mut v_x_954_: *mut crate::leanh::LeanObject,
    mut v_h__1_955_: *mut crate::leanh::LeanObject,
    mut v_h__2_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_957_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(
        v_x_953_,
        v_x_954_,
        v_h__1_955_,
        v_h__2_956_,
    );
    crate::leanh::lean_dec(v_x_953_);
    return v_res_957_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(
    mut v_motive_958_: *mut crate::leanh::LeanObject,
    mut v_x_959_: *mut crate::leanh::LeanObject,
    mut v_x_960_: *mut crate::leanh::LeanObject,
    mut v_h__1_961_: *mut crate::leanh::LeanObject,
    mut v_h__2_962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_964_: u8 = 0;
    v_zero_963_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_964_ = lean_nat_dec_eq(v_x_959_, v_zero_963_);
    if v_isZero_964_ == 1 {
        let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_962_);
        v___x_965_ = crate::leanh::lean_apply_1(v_h__1_961_, v_x_960_);
        return v___x_965_;
    } else {
        let mut v_one_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_961_);
        v_one_966_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_967_ = lean_nat_sub(v_x_959_, v_one_966_);
        v___x_968_ = crate::leanh::lean_apply_2(v_h__2_962_, v_n_967_, v_x_960_);
        return v___x_968_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___boxed(
    mut v_motive_969_: *mut crate::leanh::LeanObject,
    mut v_x_970_: *mut crate::leanh::LeanObject,
    mut v_x_971_: *mut crate::leanh::LeanObject,
    mut v_h__1_972_: *mut crate::leanh::LeanObject,
    mut v_h__2_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_974_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(
        v_motive_969_,
        v_x_970_,
        v_x_971_,
        v_h__1_972_,
        v_h__2_973_,
    );
    crate::leanh::lean_dec(v_x_970_);
    return v_res_974_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10;
    v___x_1002_ = l_Lean_mkAtom(v___x_1001_);
    return v___x_1002_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12,
    );
    v___x_1004_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5;
    v___x_1005_ = lean_array_push(v___x_1004_, v___x_1003_);
    return v___x_1005_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16;
    v___x_1017_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5;
    v___x_1018_ = lean_array_push(v___x_1017_, v___x_1016_);
    return v___x_1018_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17,
    );
    v___x_1020_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15;
    v___x_1021_ = crate::leanh::lean_box(2);
    v___x_1022_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1022_, 0, v___x_1021_);
    crate::leanh::lean_ctor_set(v___x_1022_, 1, v___x_1020_);
    crate::leanh::lean_ctor_set(v___x_1022_, 2, v___x_1019_);
    return v___x_1022_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18,
    );
    v___x_1024_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13,
    );
    v___x_1025_ = lean_array_push(v___x_1024_, v___x_1023_);
    return v___x_1025_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19,
    );
    v___x_1027_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11;
    v___x_1028_ = crate::leanh::lean_box(2);
    v___x_1029_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1029_, 0, v___x_1028_);
    crate::leanh::lean_ctor_set(v___x_1029_, 1, v___x_1027_);
    crate::leanh::lean_ctor_set(v___x_1029_, 2, v___x_1026_);
    return v___x_1029_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1030_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20,
    );
    v___x_1031_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5;
    v___x_1032_ = lean_array_push(v___x_1031_, v___x_1030_);
    return v___x_1032_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21,
    );
    v___x_1034_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9;
    v___x_1035_ = crate::leanh::lean_box(2);
    v___x_1036_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1036_, 0, v___x_1035_);
    crate::leanh::lean_ctor_set(v___x_1036_, 1, v___x_1034_);
    crate::leanh::lean_ctor_set(v___x_1036_, 2, v___x_1033_);
    return v___x_1036_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22,
    );
    v___x_1038_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5;
    v___x_1039_ = lean_array_push(v___x_1038_, v___x_1037_);
    return v___x_1039_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23,
    );
    v___x_1041_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7;
    v___x_1042_ = crate::leanh::lean_box(2);
    v___x_1043_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1043_, 0, v___x_1042_);
    crate::leanh::lean_ctor_set(v___x_1043_, 1, v___x_1041_);
    crate::leanh::lean_ctor_set(v___x_1043_, 2, v___x_1040_);
    return v___x_1043_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24,
    );
    v___x_1045_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5;
    v___x_1046_ = lean_array_push(v___x_1045_, v___x_1044_);
    return v___x_1046_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1047_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25,
    );
    v___x_1048_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4;
    v___x_1049_ = crate::leanh::lean_box(2);
    v___x_1050_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1050_, 0, v___x_1049_);
    crate::leanh::lean_ctor_set(v___x_1050_, 1, v___x_1048_);
    crate::leanh::lean_ctor_set(v___x_1050_, 2, v___x_1047_);
    return v___x_1050_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1051_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(
    mut v_x_1052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1052_);
    return v_x_1052_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(
    mut v_x_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(v_x_1053_);
    crate::leanh::lean_dec(v_x_1053_);
    return v_res_1054_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(
    mut v_n_1055_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1056_: *mut crate::leanh::LeanObject,
    mut v_i_1057_: *mut crate::leanh::LeanObject,
    mut v_j_1058_: *mut crate::leanh::LeanObject,
    mut v_hi_1059_: *mut crate::leanh::LeanObject,
    mut v_w_1060_: *mut crate::leanh::LeanObject,
    mut v_x_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1061_);
    return v_x_1061_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(
    mut v_n_1062_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1063_: *mut crate::leanh::LeanObject,
    mut v_i_1064_: *mut crate::leanh::LeanObject,
    mut v_j_1065_: *mut crate::leanh::LeanObject,
    mut v_hi_1066_: *mut crate::leanh::LeanObject,
    mut v_w_1067_: *mut crate::leanh::LeanObject,
    mut v_x_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1069_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(
        v_n_1062_,
        v_00_u03b1_1063_,
        v_i_1064_,
        v_j_1065_,
        v_hi_1066_,
        v_w_1067_,
        v_x_1068_,
    );
    crate::leanh::lean_dec(v_x_1068_);
    crate::leanh::lean_dec(v_j_1065_);
    crate::leanh::lean_dec(v_i_1064_);
    crate::leanh::lean_dec(v_n_1062_);
    return v_res_1069_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1070_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1071_;
}
pub unsafe fn _init_l_Nat_dfold___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1072_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
    mut v_n_1073_: *mut crate::leanh::LeanObject,
    mut v_f_1074_: *mut crate::leanh::LeanObject,
    mut v_j_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1078_: u8 = 0;
    let mut v_one_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1077_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1078_ = lean_nat_dec_eq(v_j_1075_, v_zero_1077_);
                if v_isZero_1078_ == 1 {
                    crate::leanh::lean_dec(v_j_1075_);
                    crate::leanh::lean_dec(v_f_1074_);
                    return v_a_1076_;
                } else {
                    v_one_1079_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1080_ = lean_nat_sub(v_j_1075_, v_one_1079_);
                    v___x_1081_ = lean_nat_sub(v_n_1073_, v_j_1075_);
                    crate::leanh::lean_dec(v_j_1075_);
                    crate::leanh::lean_inc(v_f_1074_);
                    v___x_1082_ = crate::leanh::lean_apply_3(
                        v_f_1074_,
                        v___x_1081_,
                        crate::leanh::lean_box(0),
                        v_a_1076_,
                    );
                    v_j_1075_ = v_n_1080_;
                    v_a_1076_ = v___x_1082_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg___boxed(
    mut v_n_1084_: *mut crate::leanh::LeanObject,
    mut v_f_1085_: *mut crate::leanh::LeanObject,
    mut v_j_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1084_, v_f_1085_, v_j_1086_, v_a_1087_,
    );
    crate::leanh::lean_dec(v_n_1084_);
    return v_res_1088_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(
    mut v_n_1089_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1090_: *mut crate::leanh::LeanObject,
    mut v_f_1091_: *mut crate::leanh::LeanObject,
    mut v_j_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_a_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1089_, v_f_1091_, v_j_1092_, v_a_1094_,
    );
    return v___x_1095_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(
    mut v_n_1096_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1097_: *mut crate::leanh::LeanObject,
    mut v_f_1098_: *mut crate::leanh::LeanObject,
    mut v_j_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1102_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(
        v_n_1096_,
        v_00_u03b1_1097_,
        v_f_1098_,
        v_j_1099_,
        v_a_1100_,
        v_a_1101_,
    );
    crate::leanh::lean_dec(v_n_1096_);
    return v_res_1102_;
}
pub unsafe fn l_Nat_dfold___redArg(
    mut v_n_1103_: *mut crate::leanh::LeanObject,
    mut v_f_1104_: *mut crate::leanh::LeanObject,
    mut v_init_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_1103_);
    v___x_1106_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1103_,
        v_f_1104_,
        v_n_1103_,
        v_init_1105_,
    );
    crate::leanh::lean_dec(v_n_1103_);
    return v___x_1106_;
}
pub unsafe fn l_Nat_dfold(
    mut v_n_1107_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1108_: *mut crate::leanh::LeanObject,
    mut v_f_1109_: *mut crate::leanh::LeanObject,
    mut v_init_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_1107_);
    v___x_1111_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1107_,
        v_f_1109_,
        v_n_1107_,
        v_init_1110_,
    );
    crate::leanh::lean_dec(v_n_1107_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Nat_dfoldRev___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1112_;
}
pub unsafe fn l_Nat_dfoldRev___redArg___lam__0(
    mut v_f_1113_: *mut crate::leanh::LeanObject,
    mut v_i_1114_: *mut crate::leanh::LeanObject,
    mut v_h_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ =
        crate::leanh::lean_apply_3(v_f_1113_, v_i_1114_, crate::leanh::lean_box(0), v___y_1116_);
    return v___x_1117_;
}
pub unsafe fn l_Nat_dfoldRev___redArg(
    mut v_n_1118_: *mut crate::leanh::LeanObject,
    mut v_f_1119_: *mut crate::leanh::LeanObject,
    mut v_init_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1122_: u8 = 0;
    let mut v___f_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1121_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1122_ = lean_nat_dec_eq(v_n_1118_, v_zero_1121_);
                if v_isZero_1122_ == 1 {
                    crate::leanh::lean_dec(v_f_1119_);
                    crate::leanh::lean_dec(v_n_1118_);
                    return v_init_1120_;
                } else {
                    crate::leanh::lean_inc(v_f_1119_);
                    v___f_1123_ = crate::leanh::lean_alloc_closure(
                        l_Nat_dfoldRev___redArg___lam__0 as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1123_, 0, v_f_1119_);
                    v_one_1124_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1125_ = lean_nat_sub(v_n_1118_, v_one_1124_);
                    crate::leanh::lean_dec(v_n_1118_);
                    crate::leanh::lean_inc(v_n_1125_);
                    v___x_1126_ = crate::leanh::lean_apply_3(
                        v_f_1119_,
                        v_n_1125_,
                        crate::leanh::lean_box(0),
                        v_init_1120_,
                    );
                    v_n_1118_ = v_n_1125_;
                    v_f_1119_ = v___f_1123_;
                    v_init_1120_ = v___x_1126_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_dfoldRev(
    mut v_n_1128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1129_: *mut crate::leanh::LeanObject,
    mut v_f_1130_: *mut crate::leanh::LeanObject,
    mut v_init_1131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = l_Nat_dfoldRev___redArg(v_n_1128_, v_f_1130_, v_init_1131_);
    return v___x_1132_;
}
pub unsafe fn _init_l_Nat_dfold__zero___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1133_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(
    mut v_x_1134_: *mut crate::leanh::LeanObject,
    mut v_x_1135_: *mut crate::leanh::LeanObject,
    mut v_h__1_1136_: *mut crate::leanh::LeanObject,
    mut v_h__2_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1139_: u8 = 0;
    v_zero_1138_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1139_ = lean_nat_dec_eq(v_x_1134_, v_zero_1138_);
    if v_isZero_1139_ == 1 {
        let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1137_);
        v___x_1140_ =
            crate::leanh::lean_apply_2(v_h__1_1136_, crate::leanh::lean_box(0), v_x_1135_);
        return v___x_1140_;
    } else {
        let mut v_one_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1136_);
        v_one_1141_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1142_ = lean_nat_sub(v_x_1134_, v_one_1141_);
        v___x_1143_ = crate::leanh::lean_apply_3(
            v_h__2_1137_,
            v_n_1142_,
            crate::leanh::lean_box(0),
            v_x_1135_,
        );
        return v___x_1143_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg___boxed(
    mut v_x_1144_: *mut crate::leanh::LeanObject,
    mut v_x_1145_: *mut crate::leanh::LeanObject,
    mut v_h__1_1146_: *mut crate::leanh::LeanObject,
    mut v_h__2_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(
        v_x_1144_,
        v_x_1145_,
        v_h__1_1146_,
        v_h__2_1147_,
    );
    crate::leanh::lean_dec(v_x_1144_);
    return v_res_1148_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(
    mut v_n_1149_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1150_: *mut crate::leanh::LeanObject,
    mut v_motive_1151_: *mut crate::leanh::LeanObject,
    mut v_x_1152_: *mut crate::leanh::LeanObject,
    mut v_x_1153_: *mut crate::leanh::LeanObject,
    mut v_x_1154_: *mut crate::leanh::LeanObject,
    mut v_h__1_1155_: *mut crate::leanh::LeanObject,
    mut v_h__2_1156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1158_: u8 = 0;
    v_zero_1157_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1158_ = lean_nat_dec_eq(v_x_1152_, v_zero_1157_);
    if v_isZero_1158_ == 1 {
        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1156_);
        v___x_1159_ =
            crate::leanh::lean_apply_2(v_h__1_1155_, crate::leanh::lean_box(0), v_x_1154_);
        return v___x_1159_;
    } else {
        let mut v_one_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1155_);
        v_one_1160_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1161_ = lean_nat_sub(v_x_1152_, v_one_1160_);
        v___x_1162_ = crate::leanh::lean_apply_3(
            v_h__2_1156_,
            v_n_1161_,
            crate::leanh::lean_box(0),
            v_x_1154_,
        );
        return v___x_1162_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___boxed(
    mut v_n_1163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1164_: *mut crate::leanh::LeanObject,
    mut v_motive_1165_: *mut crate::leanh::LeanObject,
    mut v_x_1166_: *mut crate::leanh::LeanObject,
    mut v_x_1167_: *mut crate::leanh::LeanObject,
    mut v_x_1168_: *mut crate::leanh::LeanObject,
    mut v_h__1_1169_: *mut crate::leanh::LeanObject,
    mut v_h__2_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(
        v_n_1163_,
        v_00_u03b1_1164_,
        v_motive_1165_,
        v_x_1166_,
        v_x_1167_,
        v_x_1168_,
        v_h__1_1169_,
        v_h__2_1170_,
    );
    crate::leanh::lean_dec(v_x_1166_);
    crate::leanh::lean_dec(v_n_1163_);
    return v_res_1171_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1172_;
}
pub unsafe fn _init_l_Nat_dfold__succ___auto__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1173_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1173_;
}
pub unsafe fn _init_l_Nat_dfold__congr___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1174_;
}
pub unsafe fn _init_l_Nat_dfold__add___auto__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1175_;
}
pub unsafe fn _init_l_Nat_dfoldRev__zero___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1176_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1176_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(
    mut v_n_1177_: *mut crate::leanh::LeanObject,
    mut v_f_1178_: *mut crate::leanh::LeanObject,
    mut v_init_1179_: *mut crate::leanh::LeanObject,
    mut v_h__1_1180_: *mut crate::leanh::LeanObject,
    mut v_h__2_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1183_: u8 = 0;
    v_zero_1182_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1183_ = lean_nat_dec_eq(v_n_1177_, v_zero_1182_);
    if v_isZero_1183_ == 1 {
        let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1181_);
        v___x_1184_ = crate::leanh::lean_apply_3(
            v_h__1_1180_,
            crate::leanh::lean_box(0),
            v_f_1178_,
            v_init_1179_,
        );
        return v___x_1184_;
    } else {
        let mut v_one_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1180_);
        v_one_1185_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1186_ = lean_nat_sub(v_n_1177_, v_one_1185_);
        v___x_1187_ = crate::leanh::lean_apply_4(
            v_h__2_1181_,
            v_n_1186_,
            crate::leanh::lean_box(0),
            v_f_1178_,
            v_init_1179_,
        );
        return v___x_1187_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg___boxed(
    mut v_n_1188_: *mut crate::leanh::LeanObject,
    mut v_f_1189_: *mut crate::leanh::LeanObject,
    mut v_init_1190_: *mut crate::leanh::LeanObject,
    mut v_h__1_1191_: *mut crate::leanh::LeanObject,
    mut v_h__2_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(
        v_n_1188_,
        v_f_1189_,
        v_init_1190_,
        v_h__1_1191_,
        v_h__2_1192_,
    );
    crate::leanh::lean_dec(v_n_1188_);
    return v_res_1193_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(
    mut v_motive_1194_: *mut crate::leanh::LeanObject,
    mut v_n_1195_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1196_: *mut crate::leanh::LeanObject,
    mut v_f_1197_: *mut crate::leanh::LeanObject,
    mut v_init_1198_: *mut crate::leanh::LeanObject,
    mut v_h__1_1199_: *mut crate::leanh::LeanObject,
    mut v_h__2_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1202_: u8 = 0;
    v_zero_1201_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1202_ = lean_nat_dec_eq(v_n_1195_, v_zero_1201_);
    if v_isZero_1202_ == 1 {
        let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1200_);
        v___x_1203_ = crate::leanh::lean_apply_3(
            v_h__1_1199_,
            crate::leanh::lean_box(0),
            v_f_1197_,
            v_init_1198_,
        );
        return v___x_1203_;
    } else {
        let mut v_one_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1199_);
        v_one_1204_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1205_ = lean_nat_sub(v_n_1195_, v_one_1204_);
        v___x_1206_ = crate::leanh::lean_apply_4(
            v_h__2_1200_,
            v_n_1205_,
            crate::leanh::lean_box(0),
            v_f_1197_,
            v_init_1198_,
        );
        return v___x_1206_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___boxed(
    mut v_motive_1207_: *mut crate::leanh::LeanObject,
    mut v_n_1208_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1209_: *mut crate::leanh::LeanObject,
    mut v_f_1210_: *mut crate::leanh::LeanObject,
    mut v_init_1211_: *mut crate::leanh::LeanObject,
    mut v_h__1_1212_: *mut crate::leanh::LeanObject,
    mut v_h__2_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1214_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(
        v_motive_1207_,
        v_n_1208_,
        v_00_u03b1_1209_,
        v_f_1210_,
        v_init_1211_,
        v_h__1_1212_,
        v_h__2_1213_,
    );
    crate::leanh::lean_dec(v_n_1208_);
    return v_res_1214_;
}
pub unsafe fn _init_l_Nat_dfoldRev__succ___auto__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1215_;
}
pub unsafe fn _init_l_Nat_dfoldRev__congr___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1216_;
}
pub unsafe fn _init_l_Nat_dfoldRev__add___auto__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26,
    );
    return v___x_1217_;
}
pub unsafe fn l_Prod_foldI___redArg___lam__0(
    mut v_fst_1218_: *mut crate::leanh::LeanObject,
    mut v_f_1219_: *mut crate::leanh::LeanObject,
    mut v_j_1220_: *mut crate::leanh::LeanObject,
    mut v_x_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ = lean_nat_add(v_fst_1218_, v_j_1220_);
    v___x_1224_ = crate::leanh::lean_apply_4(
        v_f_1219_,
        v___x_1223_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___y_1222_,
    );
    return v___x_1224_;
}
pub unsafe fn l_Prod_foldI___redArg___lam__0___boxed(
    mut v_fst_1225_: *mut crate::leanh::LeanObject,
    mut v_f_1226_: *mut crate::leanh::LeanObject,
    mut v_j_1227_: *mut crate::leanh::LeanObject,
    mut v_x_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1230_ =
        l_Prod_foldI___redArg___lam__0(v_fst_1225_, v_f_1226_, v_j_1227_, v_x_1228_, v___y_1229_);
    crate::leanh::lean_dec(v_j_1227_);
    crate::leanh::lean_dec(v_fst_1225_);
    return v_res_1230_;
}
pub unsafe fn l_Prod_foldI___redArg(
    mut v_i_1231_: *mut crate::leanh::LeanObject,
    mut v_f_1232_: *mut crate::leanh::LeanObject,
    mut v_init_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1234_ = crate::leanh::lean_ctor_get(v_i_1231_, 0);
    crate::leanh::lean_inc_n(v_fst_1234_, 2);
    v_snd_1235_ = crate::leanh::lean_ctor_get(v_i_1231_, 1);
    crate::leanh::lean_inc(v_snd_1235_);
    crate::leanh::lean_dec_ref(v_i_1231_);
    v___f_1236_ = crate::leanh::lean_alloc_closure(
        l_Prod_foldI___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1236_, 0, v_fst_1234_);
    crate::leanh::lean_closure_set(v___f_1236_, 1, v_f_1232_);
    v___x_1237_ = lean_nat_sub(v_snd_1235_, v_fst_1234_);
    crate::leanh::lean_dec(v_fst_1234_);
    crate::leanh::lean_dec(v_snd_1235_);
    crate::leanh::lean_inc(v___x_1237_);
    v___x_1238_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v___x_1237_,
        v___f_1236_,
        v___x_1237_,
        v_init_1233_,
    );
    crate::leanh::lean_dec(v___x_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Prod_foldI(
    mut v_00_u03b1_1239_: *mut crate::leanh::LeanObject,
    mut v_i_1240_: *mut crate::leanh::LeanObject,
    mut v_f_1241_: *mut crate::leanh::LeanObject,
    mut v_init_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1243_ = crate::leanh::lean_ctor_get(v_i_1240_, 0);
    crate::leanh::lean_inc_n(v_fst_1243_, 2);
    v_snd_1244_ = crate::leanh::lean_ctor_get(v_i_1240_, 1);
    crate::leanh::lean_inc(v_snd_1244_);
    crate::leanh::lean_dec_ref(v_i_1240_);
    v___f_1245_ = crate::leanh::lean_alloc_closure(
        l_Prod_foldI___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1245_, 0, v_fst_1243_);
    crate::leanh::lean_closure_set(v___f_1245_, 1, v_f_1241_);
    v___x_1246_ = lean_nat_sub(v_snd_1244_, v_fst_1243_);
    crate::leanh::lean_dec(v_fst_1243_);
    crate::leanh::lean_dec(v_snd_1244_);
    crate::leanh::lean_inc(v___x_1246_);
    v___x_1247_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v___x_1246_,
        v___f_1245_,
        v___x_1246_,
        v_init_1242_,
    );
    crate::leanh::lean_dec(v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Prod_anyI___lam__0(
    mut v_fst_1248_: *mut crate::leanh::LeanObject,
    mut v_f_1249_: *mut crate::leanh::LeanObject,
    mut v_j_1250_: *mut crate::leanh::LeanObject,
    mut v_x_1251_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    v___x_1252_ = lean_nat_add(v_fst_1248_, v_j_1250_);
    v___x_1253_ = crate::leanh::lean_apply_3(
        v_f_1249_,
        v___x_1252_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    v___x_1254_ = (crate::leanh::lean_unbox(v___x_1253_) as u8);
    return v___x_1254_;
}
pub unsafe fn l_Prod_anyI___lam__0___boxed(
    mut v_fst_1255_: *mut crate::leanh::LeanObject,
    mut v_f_1256_: *mut crate::leanh::LeanObject,
    mut v_j_1257_: *mut crate::leanh::LeanObject,
    mut v_x_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1259_: u8 = 0;
    let mut v_r_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Prod_anyI___lam__0(v_fst_1255_, v_f_1256_, v_j_1257_, v_x_1258_);
    crate::leanh::lean_dec(v_j_1257_);
    crate::leanh::lean_dec(v_fst_1255_);
    v_r_1260_ = crate::leanh::lean_box((v_res_1259_) as usize);
    return v_r_1260_;
}
pub unsafe fn l_Prod_anyI(
    mut v_i_1261_: *mut crate::leanh::LeanObject,
    mut v_f_1262_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    v_fst_1263_ = crate::leanh::lean_ctor_get(v_i_1261_, 0);
    crate::leanh::lean_inc_n(v_fst_1263_, 2);
    v_snd_1264_ = crate::leanh::lean_ctor_get(v_i_1261_, 1);
    crate::leanh::lean_inc(v_snd_1264_);
    crate::leanh::lean_dec_ref(v_i_1261_);
    v___f_1265_ = crate::leanh::lean_alloc_closure(
        l_Prod_anyI___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1265_, 0, v_fst_1263_);
    crate::leanh::lean_closure_set(v___f_1265_, 1, v_f_1262_);
    v___x_1266_ = lean_nat_sub(v_snd_1264_, v_fst_1263_);
    crate::leanh::lean_dec(v_fst_1263_);
    crate::leanh::lean_dec(v_snd_1264_);
    crate::leanh::lean_inc(v___x_1266_);
    v___x_1267_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(
        v___x_1266_,
        v___f_1265_,
        v___x_1266_,
    );
    crate::leanh::lean_dec(v___x_1266_);
    return v___x_1267_;
}
pub unsafe fn l_Prod_anyI___boxed(
    mut v_i_1268_: *mut crate::leanh::LeanObject,
    mut v_f_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1270_: u8 = 0;
    let mut v_r_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Prod_anyI(v_i_1268_, v_f_1269_);
    v_r_1271_ = crate::leanh::lean_box((v_res_1270_) as usize);
    return v_r_1271_;
}
pub unsafe fn l_Prod_allI(
    mut v_i_1272_: *mut crate::leanh::LeanObject,
    mut v_f_1273_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    v_fst_1274_ = crate::leanh::lean_ctor_get(v_i_1272_, 0);
    crate::leanh::lean_inc_n(v_fst_1274_, 2);
    v_snd_1275_ = crate::leanh::lean_ctor_get(v_i_1272_, 1);
    crate::leanh::lean_inc(v_snd_1275_);
    crate::leanh::lean_dec_ref(v_i_1272_);
    v___f_1276_ = crate::leanh::lean_alloc_closure(
        l_Prod_anyI___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1276_, 0, v_fst_1274_);
    crate::leanh::lean_closure_set(v___f_1276_, 1, v_f_1273_);
    v___x_1277_ = lean_nat_sub(v_snd_1275_, v_fst_1274_);
    crate::leanh::lean_dec(v_fst_1274_);
    crate::leanh::lean_dec(v_snd_1275_);
    crate::leanh::lean_inc(v___x_1277_);
    v___x_1278_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(
        v___x_1277_,
        v___f_1276_,
        v___x_1277_,
    );
    crate::leanh::lean_dec(v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Prod_allI___boxed(
    mut v_i_1279_: *mut crate::leanh::LeanObject,
    mut v_f_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1281_: u8 = 0;
    let mut v_r_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Prod_allI(v_i_1279_, v_f_1280_);
    v_r_1282_ = crate::leanh::lean_box((v_res_1281_) as usize);
    return v_r_1282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Fold(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_FinRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Fold(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1();
    crate::leanh::lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1);
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9,
    );
    l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3,
    );
    l_Nat_dfold___auto__1 = _init_l_Nat_dfold___auto__1();
    crate::leanh::lean_mark_persistent(l_Nat_dfold___auto__1);
    l_Nat_dfoldRev___auto__1 = _init_l_Nat_dfoldRev___auto__1();
    crate::leanh::lean_mark_persistent(l_Nat_dfoldRev___auto__1);
    l_Nat_dfold__zero___auto__1 = _init_l_Nat_dfold__zero___auto__1();
    crate::leanh::lean_mark_persistent(l_Nat_dfold__zero___auto__1);
    l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5,
    );
    l_Nat_dfold__succ___auto__3 = _init_l_Nat_dfold__succ___auto__3();
    crate::leanh::lean_mark_persistent(l_Nat_dfold__succ___auto__3);
    l_Nat_dfold__congr___auto__1 = _init_l_Nat_dfold__congr___auto__1();
    crate::leanh::lean_mark_persistent(l_Nat_dfold__congr___auto__1);
    l_Nat_dfold__add___auto__5 = _init_l_Nat_dfold__add___auto__5();
    crate::leanh::lean_mark_persistent(l_Nat_dfold__add___auto__5);
    l_Nat_dfoldRev__zero___auto__1 = _init_l_Nat_dfoldRev__zero___auto__1();
    crate::leanh::lean_mark_persistent(l_Nat_dfoldRev__zero___auto__1);
    l_Nat_dfoldRev__succ___auto__3 = _init_l_Nat_dfoldRev__succ___auto__3();
    crate::leanh::lean_mark_persistent(l_Nat_dfoldRev__succ___auto__3);
    l_Nat_dfoldRev__congr___auto__1 = _init_l_Nat_dfoldRev__congr___auto__1();
    crate::leanh::lean_mark_persistent(l_Nat_dfoldRev__congr___auto__1);
    l_Nat_dfoldRev__add___auto__5 = _init_l_Nat_dfoldRev__add___auto__5();
    crate::leanh::lean_mark_persistent(l_Nat_dfoldRev__add___auto__5);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Fold(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_FinRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Fold(builtin);
}
