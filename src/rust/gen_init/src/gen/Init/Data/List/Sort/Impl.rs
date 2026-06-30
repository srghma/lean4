// Lean compiler output
// Module: Init.Data.List.Sort.Impl
// Imports: Init.Data.List.Sort.Basic Init.Data.List.Sort.Basic Init.Data.List.Sort.Lemmas Init.Data.Nat.Linear
use crate::ffi::{
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_shiftr, lean_nat_sub,
    lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverseAux___redArg;
use crate::r#gen::Init::Data::List::Sort::Basic::{
    initialize_Init_Data_List_Sort_Basic, l_List_MergeSort_Internal_splitInTwo___redArg,
    runtime_initialize_Init_Data_List_Sort_Basic,
};
use crate::r#gen::Init::Data::List::Sort::Lemmas::{
    initialize_Init_Data_List_Sort_Lemmas, runtime_initialize_Init_Data_List_Sort_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Prelude::{l_Lean_mkAtom, l_List_lengthTR___redArg};
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value:
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value:
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
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value:
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
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value)
            as *mut leanh::LeanObject,
        14997215300048349804 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [102, 117, 110, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_0:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_1:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_2:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value)
            as *mut leanh::LeanObject,
        7043493786777132025 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value)
        as *mut leanh::LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_0:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_1:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_2:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value:
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
            l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value)
            as *mut leanh::LeanObject,
        16077784126176397009 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value)
            as *mut leanh::LeanObject,
        7839396180116328695 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value)
            as *mut leanh::LeanObject,
        10300200614825825839 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [61, 62, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 137, 164, 95, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value:
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
        core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value)
            as *mut leanh::LeanObject,
        8748957123817046895 as *mut leanh::LeanObject,
    ],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value)
        as *mut leanh::LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 137, 164, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value)
        as *mut leanh::LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_List_MergeSort_Internal_mergeSortTR___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(
    mut v_le_611_: *mut leanh::LeanObject,
    mut v_a_612_: *mut leanh::LeanObject,
    mut v_a_613_: *mut leanh::LeanObject,
    mut v_a_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: u8 = 0;
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_625_: u8 = 0;
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_630_: u8 = 0;
    let mut v_unused_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_635_: u8 = 0;
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut v_unused_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_612_) == 0 {
                    leanh::lean_dec_ref(v_le_611_);
                    v___x_615_ = l_List_reverseAux___redArg(v_a_614_, v_a_613_);
                    return v___x_615_;
                } else {
                    if leanh::lean_obj_tag(v_a_613_) == 0 {
                        leanh::lean_dec_ref(v_le_611_);
                        v___x_616_ = l_List_reverseAux___redArg(v_a_614_, v_a_612_);
                        return v___x_616_;
                    } else {
                        v_head_617_ = leanh::lean_ctor_get(v_a_612_, 0);
                        v_tail_618_ = leanh::lean_ctor_get(v_a_612_, 1);
                        v_head_619_ = leanh::lean_ctor_get(v_a_613_, 0);
                        v_tail_620_ = leanh::lean_ctor_get(v_a_613_, 1);
                        leanh::lean_inc_ref(v_le_611_);
                        leanh::lean_inc(v_head_619_);
                        leanh::lean_inc(v_head_617_);
                        v___x_621_ =
                            leanh::lean_apply_2(v_le_611_, v_head_617_, v_head_619_);
                        v___x_622_ = (leanh::lean_unbox(v___x_621_) as u8);
                        if v___x_622_ == 0 {
                            leanh::lean_inc(v_tail_620_);
                            leanh::lean_inc(v_head_619_);
                            v_isSharedCheck_630_ =
                                (!leanh::lean_is_exclusive(v_a_613_)) as u8;
                            if v_isSharedCheck_630_ == 0 {
                                v_unused_631_ = leanh::lean_ctor_get(v_a_613_, 1);
                                leanh::lean_dec(v_unused_631_);
                                v_unused_632_ = leanh::lean_ctor_get(v_a_613_, 0);
                                leanh::lean_dec(v_unused_632_);
                                v___x_624_ = v_a_613_;
                                v_isShared_625_ = v_isSharedCheck_630_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_613_);
                                v___x_624_ = leanh::lean_box(0);
                                v_isShared_625_ = v_isSharedCheck_630_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_inc(v_tail_618_);
                            leanh::lean_inc(v_head_617_);
                            v_isSharedCheck_640_ =
                                (!leanh::lean_is_exclusive(v_a_612_)) as u8;
                            if v_isSharedCheck_640_ == 0 {
                                v_unused_641_ = leanh::lean_ctor_get(v_a_612_, 1);
                                leanh::lean_dec(v_unused_641_);
                                v_unused_642_ = leanh::lean_ctor_get(v_a_612_, 0);
                                leanh::lean_dec(v_unused_642_);
                                v___x_634_ = v_a_612_;
                                v_isShared_635_ = v_isSharedCheck_640_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_612_);
                                v___x_634_ = leanh::lean_box(0);
                                v_isShared_635_ = v_isSharedCheck_640_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_625_ == 0 {
                    leanh::lean_ctor_set(v___x_624_, 1, v_a_614_);
                    v___x_627_ = v___x_624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_629_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_629_, 0, v_head_619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_614_);
                    v___x_627_ = v_reuseFailAlloc_629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_613_ = v_tail_620_;
                v_a_614_ = v___x_627_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_635_ == 0 {
                    leanh::lean_ctor_set(v___x_634_, 1, v_a_614_);
                    v___x_637_ = v___x_634_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_639_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_639_, 0, v_head_617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_639_, 1, v_a_614_);
                    v___x_637_ = v_reuseFailAlloc_639_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_612_ = v_tail_618_;
                v_a_614_ = v___x_637_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go(
    mut v_00_u03b1_643_: *mut leanh::LeanObject,
    mut v_le_644_: *mut leanh::LeanObject,
    mut v_a_645_: *mut leanh::LeanObject,
    mut v_a_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_648_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(
            v_le_644_, v_a_645_, v_a_646_, v_a_647_,
        );
    return v___x_648_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___redArg(
    mut v_x_649_: *mut leanh::LeanObject,
    mut v_x_650_: *mut leanh::LeanObject,
    mut v_x_651_: *mut leanh::LeanObject,
    mut v_h__1_652_: *mut leanh::LeanObject,
    mut v_h__2_653_: *mut leanh::LeanObject,
    mut v_h__3_654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_649_) == 0 {
        let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_654_);
        leanh::lean_dec(v_h__2_653_);
        v___x_655_ = leanh::lean_apply_2(v_h__1_652_, v_x_650_, v_x_651_);
        return v___x_655_;
    } else {
        leanh::lean_dec(v_h__1_652_);
        if leanh::lean_obj_tag(v_x_650_) == 0 {
            let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_654_);
            v___x_656_ = leanh::lean_apply_3(
                v_h__2_653_,
                v_x_649_,
                v_x_651_,
                leanh::lean_box(0),
            );
            return v___x_656_;
        } else {
            let mut v_head_657_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_658_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_659_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_660_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_653_);
            v_head_657_ = leanh::lean_ctor_get(v_x_649_, 0);
            leanh::lean_inc(v_head_657_);
            v_tail_658_ = leanh::lean_ctor_get(v_x_649_, 1);
            leanh::lean_inc(v_tail_658_);
            leanh::lean_dec_ref_known(v_x_649_, 2);
            v_head_659_ = leanh::lean_ctor_get(v_x_650_, 0);
            leanh::lean_inc(v_head_659_);
            v_tail_660_ = leanh::lean_ctor_get(v_x_650_, 1);
            leanh::lean_inc(v_tail_660_);
            leanh::lean_dec_ref_known(v_x_650_, 2);
            v___x_661_ = leanh::lean_apply_5(
                v_h__3_654_,
                v_head_657_,
                v_tail_658_,
                v_head_659_,
                v_tail_660_,
                v_x_651_,
            );
            return v___x_661_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(
    mut v_00_u03b1_662_: *mut leanh::LeanObject,
    mut v_motive_663_: *mut leanh::LeanObject,
    mut v_x_664_: *mut leanh::LeanObject,
    mut v_x_665_: *mut leanh::LeanObject,
    mut v_x_666_: *mut leanh::LeanObject,
    mut v_h__1_667_: *mut leanh::LeanObject,
    mut v_h__2_668_: *mut leanh::LeanObject,
    mut v_h__3_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_664_) == 0 {
        let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_669_);
        leanh::lean_dec(v_h__2_668_);
        v___x_670_ = leanh::lean_apply_2(v_h__1_667_, v_x_665_, v_x_666_);
        return v___x_670_;
    } else {
        leanh::lean_dec(v_h__1_667_);
        if leanh::lean_obj_tag(v_x_665_) == 0 {
            let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_669_);
            v___x_671_ = leanh::lean_apply_3(
                v_h__2_668_,
                v_x_664_,
                v_x_666_,
                leanh::lean_box(0),
            );
            return v___x_671_;
        } else {
            let mut v_head_672_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_673_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_674_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_675_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_668_);
            v_head_672_ = leanh::lean_ctor_get(v_x_664_, 0);
            leanh::lean_inc(v_head_672_);
            v_tail_673_ = leanh::lean_ctor_get(v_x_664_, 1);
            leanh::lean_inc(v_tail_673_);
            leanh::lean_dec_ref_known(v_x_664_, 2);
            v_head_674_ = leanh::lean_ctor_get(v_x_665_, 0);
            leanh::lean_inc(v_head_674_);
            v_tail_675_ = leanh::lean_ctor_get(v_x_665_, 1);
            leanh::lean_inc(v_tail_675_);
            leanh::lean_dec_ref_known(v_x_665_, 2);
            v___x_676_ = leanh::lean_apply_5(
                v_h__3_669_,
                v_head_672_,
                v_tail_673_,
                v_head_674_,
                v_tail_675_,
                v_x_666_,
            );
            return v___x_676_;
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_mergeTR___redArg(
    mut v_l_u2081_677_: *mut leanh::LeanObject,
    mut v_l_u2082_678_: *mut leanh::LeanObject,
    mut v_le_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = leanh::lean_box(0);
    v___x_681_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(
            v_le_679_,
            v_l_u2081_677_,
            v_l_u2082_678_,
            v___x_680_,
        );
    return v___x_681_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeTR(
    mut v_00_u03b1_682_: *mut leanh::LeanObject,
    mut v_l_u2081_683_: *mut leanh::LeanObject,
    mut v_l_u2082_684_: *mut leanh::LeanObject,
    mut v_le_685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_686_ =
        l_List_MergeSort_Internal_mergeTR___redArg(v_l_u2081_683_, v_l_u2082_684_, v_le_685_);
    return v___x_686_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter___redArg(
    mut v_xs_687_: *mut leanh::LeanObject,
    mut v_ys_688_: *mut leanh::LeanObject,
    mut v_h__1_689_: *mut leanh::LeanObject,
    mut v_h__2_690_: *mut leanh::LeanObject,
    mut v_h__3_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_687_) == 0 {
        let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_691_);
        leanh::lean_dec(v_h__2_690_);
        v___x_692_ = leanh::lean_apply_1(v_h__1_689_, v_ys_688_);
        return v___x_692_;
    } else {
        leanh::lean_dec(v_h__1_689_);
        if leanh::lean_obj_tag(v_ys_688_) == 0 {
            let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_691_);
            v___x_693_ =
                leanh::lean_apply_2(v_h__2_690_, v_xs_687_, leanh::lean_box(0));
            return v___x_693_;
        } else {
            let mut v_head_694_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_695_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_696_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_697_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_690_);
            v_head_694_ = leanh::lean_ctor_get(v_xs_687_, 0);
            leanh::lean_inc(v_head_694_);
            v_tail_695_ = leanh::lean_ctor_get(v_xs_687_, 1);
            leanh::lean_inc(v_tail_695_);
            leanh::lean_dec_ref_known(v_xs_687_, 2);
            v_head_696_ = leanh::lean_ctor_get(v_ys_688_, 0);
            leanh::lean_inc(v_head_696_);
            v_tail_697_ = leanh::lean_ctor_get(v_ys_688_, 1);
            leanh::lean_inc(v_tail_697_);
            leanh::lean_dec_ref_known(v_ys_688_, 2);
            v___x_698_ = leanh::lean_apply_4(
                v_h__3_691_,
                v_head_694_,
                v_tail_695_,
                v_head_696_,
                v_tail_697_,
            );
            return v___x_698_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter(
    mut v_00_u03b1_699_: *mut leanh::LeanObject,
    mut v_motive_700_: *mut leanh::LeanObject,
    mut v_xs_701_: *mut leanh::LeanObject,
    mut v_ys_702_: *mut leanh::LeanObject,
    mut v_h__1_703_: *mut leanh::LeanObject,
    mut v_h__2_704_: *mut leanh::LeanObject,
    mut v_h__3_705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_701_) == 0 {
        let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_705_);
        leanh::lean_dec(v_h__2_704_);
        v___x_706_ = leanh::lean_apply_1(v_h__1_703_, v_ys_702_);
        return v___x_706_;
    } else {
        leanh::lean_dec(v_h__1_703_);
        if leanh::lean_obj_tag(v_ys_702_) == 0 {
            let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_705_);
            v___x_707_ =
                leanh::lean_apply_2(v_h__2_704_, v_xs_701_, leanh::lean_box(0));
            return v___x_707_;
        } else {
            let mut v_head_708_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_709_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_710_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_711_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_704_);
            v_head_708_ = leanh::lean_ctor_get(v_xs_701_, 0);
            leanh::lean_inc(v_head_708_);
            v_tail_709_ = leanh::lean_ctor_get(v_xs_701_, 1);
            leanh::lean_inc(v_tail_709_);
            leanh::lean_dec_ref_known(v_xs_701_, 2);
            v_head_710_ = leanh::lean_ctor_get(v_ys_702_, 0);
            leanh::lean_inc(v_head_710_);
            v_tail_711_ = leanh::lean_ctor_get(v_ys_702_, 1);
            leanh::lean_inc(v_tail_711_);
            leanh::lean_dec_ref_known(v_ys_702_, 2);
            v___x_712_ = leanh::lean_apply_4(
                v_h__3_705_,
                v_head_708_,
                v_tail_709_,
                v_head_710_,
                v_tail_711_,
            );
            return v___x_712_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(
    mut v_a_713_: *mut leanh::LeanObject,
    mut v_a_714_: *mut leanh::LeanObject,
    mut v_a_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_719_: u8 = 0;
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v_one_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_729_: u8 = 0;
    let mut v_unused_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_713_) == 1 {
                    v_head_716_ = leanh::lean_ctor_get(v_a_713_, 0);
                    v_tail_717_ = leanh::lean_ctor_get(v_a_713_, 1);
                    v_zero_718_ = leanh::lean_unsigned_to_nat(0);
                    v_isZero_719_ = lean_nat_dec_eq(v_a_714_, v_zero_718_);
                    if v_isZero_719_ == 0 {
                        leanh::lean_inc(v_tail_717_);
                        leanh::lean_inc(v_head_716_);
                        v_isSharedCheck_729_ = (!leanh::lean_is_exclusive(v_a_713_)) as u8;
                        if v_isSharedCheck_729_ == 0 {
                            v_unused_730_ = leanh::lean_ctor_get(v_a_713_, 1);
                            leanh::lean_dec(v_unused_730_);
                            v_unused_731_ = leanh::lean_ctor_get(v_a_713_, 0);
                            leanh::lean_dec(v_unused_731_);
                            v___x_721_ = v_a_713_;
                            v_isShared_722_ = v_isSharedCheck_729_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_713_);
                            v___x_721_ = leanh::lean_box(0);
                            v_isShared_722_ = v_isSharedCheck_729_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_714_);
                        v___x_732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_732_, 0, v_a_715_);
                        leanh::lean_ctor_set(v___x_732_, 1, v_a_713_);
                        return v___x_732_;
                    }
                } else {
                    leanh::lean_dec(v_a_714_);
                    v___x_733_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_733_, 0, v_a_715_);
                    leanh::lean_ctor_set(v___x_733_, 1, v_a_713_);
                    return v___x_733_;
                }
            }
            1 => {
                v_one_723_ = leanh::lean_unsigned_to_nat(1);
                v_n_724_ = lean_nat_sub(v_a_714_, v_one_723_);
                leanh::lean_dec(v_a_714_);
                if v_isShared_722_ == 0 {
                    leanh::lean_ctor_set(v___x_721_, 1, v_a_715_);
                    v___x_726_ = v___x_721_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_728_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_728_, 0, v_head_716_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_728_, 1, v_a_715_);
                    v___x_726_ = v_reuseFailAlloc_728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_713_ = v_tail_717_;
                v_a_714_ = v_n_724_;
                v_a_715_ = v___x_726_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go(
    mut v_00_u03b1_734_: *mut leanh::LeanObject,
    mut v_a_735_: *mut leanh::LeanObject,
    mut v_a_736_: *mut leanh::LeanObject,
    mut v_a_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(
            v_a_735_, v_a_736_, v_a_737_,
        );
    return v___x_738_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevAt___redArg(
    mut v_n_739_: *mut leanh::LeanObject,
    mut v_l_740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = leanh::lean_box(0);
    v___x_742_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(
            v_l_740_, v_n_739_, v___x_741_,
        );
    return v___x_742_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevAt(
    mut v_00_u03b1_743_: *mut leanh::LeanObject,
    mut v_n_744_: *mut leanh::LeanObject,
    mut v_l_745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = l_List_MergeSort_Internal_splitRevAt___redArg(v_n_744_, v_l_745_);
    return v___x_746_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___redArg(
    mut v_x_747_: *mut leanh::LeanObject,
    mut v_x_748_: *mut leanh::LeanObject,
    mut v_x_749_: *mut leanh::LeanObject,
    mut v_h__1_750_: *mut leanh::LeanObject,
    mut v_h__2_751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_747_) == 1 {
        let mut v_head_752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_755_: u8 = 0;
        v_head_752_ = leanh::lean_ctor_get(v_x_747_, 0);
        v_tail_753_ = leanh::lean_ctor_get(v_x_747_, 1);
        v_zero_754_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_755_ = lean_nat_dec_eq(v_x_748_, v_zero_754_);
        if v_isZero_755_ == 0 {
            let mut v_one_756_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_757_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_753_);
            leanh::lean_inc(v_head_752_);
            leanh::lean_dec_ref_known(v_x_747_, 2);
            leanh::lean_dec(v_h__2_751_);
            v_one_756_ = leanh::lean_unsigned_to_nat(1);
            v_n_757_ = lean_nat_sub(v_x_748_, v_one_756_);
            leanh::lean_dec(v_x_748_);
            v___x_758_ = leanh::lean_apply_4(
                v_h__1_750_,
                v_head_752_,
                v_tail_753_,
                v_n_757_,
                v_x_749_,
            );
            return v___x_758_;
        } else {
            let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_750_);
            v___x_759_ = leanh::lean_apply_4(
                v_h__2_751_,
                v_x_747_,
                v_x_748_,
                v_x_749_,
                leanh::lean_box(0),
            );
            return v___x_759_;
        }
    } else {
        let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_750_);
        v___x_760_ = leanh::lean_apply_4(
            v_h__2_751_,
            v_x_747_,
            v_x_748_,
            v_x_749_,
            leanh::lean_box(0),
        );
        return v___x_760_;
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter(
    mut v_00_u03b1_761_: *mut leanh::LeanObject,
    mut v_motive_762_: *mut leanh::LeanObject,
    mut v_x_763_: *mut leanh::LeanObject,
    mut v_x_764_: *mut leanh::LeanObject,
    mut v_x_765_: *mut leanh::LeanObject,
    mut v_h__1_766_: *mut leanh::LeanObject,
    mut v_h__2_767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_763_) == 1 {
        let mut v_head_768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_771_: u8 = 0;
        v_head_768_ = leanh::lean_ctor_get(v_x_763_, 0);
        v_tail_769_ = leanh::lean_ctor_get(v_x_763_, 1);
        v_zero_770_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_771_ = lean_nat_dec_eq(v_x_764_, v_zero_770_);
        if v_isZero_771_ == 0 {
            let mut v_one_772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_773_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_769_);
            leanh::lean_inc(v_head_768_);
            leanh::lean_dec_ref_known(v_x_763_, 2);
            leanh::lean_dec(v_h__2_767_);
            v_one_772_ = leanh::lean_unsigned_to_nat(1);
            v_n_773_ = lean_nat_sub(v_x_764_, v_one_772_);
            leanh::lean_dec(v_x_764_);
            v___x_774_ = leanh::lean_apply_4(
                v_h__1_766_,
                v_head_768_,
                v_tail_769_,
                v_n_773_,
                v_x_765_,
            );
            return v___x_774_;
        } else {
            let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_766_);
            v___x_775_ = leanh::lean_apply_4(
                v_h__2_767_,
                v_x_763_,
                v_x_764_,
                v_x_765_,
                leanh::lean_box(0),
            );
            return v___x_775_;
        }
    } else {
        let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_766_);
        v___x_776_ = leanh::lean_apply_4(
            v_h__2_767_,
            v_x_763_,
            v_x_764_,
            v_x_765_,
            leanh::lean_box(0),
        );
        return v___x_776_;
    }
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_803_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10;
    v___x_804_ = l_Lean_mkAtom(v___x_803_);
    return v___x_804_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12,
    );
    v___x_806_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_807_ = lean_array_push(v___x_806_, v___x_805_);
    return v___x_807_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15;
    v___x_816_ = l_Lean_mkAtom(v___x_815_);
    return v___x_816_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17,
    );
    v___x_818_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_819_ = lean_array_push(v___x_818_, v___x_817_);
    return v___x_819_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21;
    v___x_828_ = lean_string_utf8_byte_size(v___x_827_);
    return v___x_828_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22,
    );
    v___x_830_ = leanh::lean_unsigned_to_nat(0);
    v___x_831_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21;
    v___x_832_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_832_, 0, v___x_831_);
    leanh::lean_ctor_set(v___x_832_, 1, v___x_830_);
    leanh::lean_ctor_set(v___x_832_, 2, v___x_829_);
    return v___x_832_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = leanh::lean_box(0);
    v___x_836_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24;
    v___x_837_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23,
    );
    v___x_838_ = leanh::lean_box(2);
    v___x_839_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_839_, 0, v___x_838_);
    leanh::lean_ctor_set(v___x_839_, 1, v___x_837_);
    leanh::lean_ctor_set(v___x_839_, 2, v___x_836_);
    leanh::lean_ctor_set(v___x_839_, 3, v___x_835_);
    return v___x_839_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25,
    );
    v___x_841_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_842_ = lean_array_push(v___x_841_, v___x_840_);
    return v___x_842_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27;
    v___x_845_ = lean_string_utf8_byte_size(v___x_844_);
    return v___x_845_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28,
    );
    v___x_847_ = leanh::lean_unsigned_to_nat(0);
    v___x_848_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27;
    v___x_849_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_849_, 0, v___x_848_);
    leanh::lean_ctor_set(v___x_849_, 1, v___x_847_);
    leanh::lean_ctor_set(v___x_849_, 2, v___x_846_);
    return v___x_849_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = leanh::lean_box(0);
    v___x_853_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30;
    v___x_854_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29,
    );
    v___x_855_ = leanh::lean_box(2);
    v___x_856_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_856_, 0, v___x_855_);
    leanh::lean_ctor_set(v___x_856_, 1, v___x_854_);
    leanh::lean_ctor_set(v___x_856_, 2, v___x_853_);
    leanh::lean_ctor_set(v___x_856_, 3, v___x_852_);
    return v___x_856_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31,
    );
    v___x_858_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26,
    );
    v___x_859_ = lean_array_push(v___x_858_, v___x_857_);
    return v___x_859_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32,
    );
    v___x_861_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9;
    v___x_862_ = leanh::lean_box(2);
    v___x_863_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_863_, 0, v___x_862_);
    leanh::lean_ctor_set(v___x_863_, 1, v___x_861_);
    leanh::lean_ctor_set(v___x_863_, 2, v___x_860_);
    return v___x_863_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33,
    );
    v___x_865_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_866_ = lean_array_push(v___x_865_, v___x_864_);
    return v___x_866_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35;
    v___x_872_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34,
    );
    v___x_873_ = lean_array_push(v___x_872_, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37;
    v___x_876_ = l_Lean_mkAtom(v___x_875_);
    return v___x_876_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38,
    );
    v___x_878_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36,
    );
    v___x_879_ = lean_array_push(v___x_878_, v___x_877_);
    return v___x_879_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42;
    v___x_885_ = l_Lean_mkAtom(v___x_884_);
    return v___x_885_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43,
    );
    v___x_887_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26,
    );
    v___x_888_ = lean_array_push(v___x_887_, v___x_886_);
    return v___x_888_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31,
    );
    v___x_890_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44,
    );
    v___x_891_ = lean_array_push(v___x_890_, v___x_889_);
    return v___x_891_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_892_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45,
    );
    v___x_893_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41;
    v___x_894_ = leanh::lean_box(2);
    v___x_895_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_895_, 0, v___x_894_);
    leanh::lean_ctor_set(v___x_895_, 1, v___x_893_);
    leanh::lean_ctor_set(v___x_895_, 2, v___x_892_);
    return v___x_895_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47()
-> *mut leanh::LeanObject {
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46,
    );
    v___x_897_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39,
    );
    v___x_898_ = lean_array_push(v___x_897_, v___x_896_);
    return v___x_898_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47,
    );
    v___x_900_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20;
    v___x_901_ = leanh::lean_box(2);
    v___x_902_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_902_, 0, v___x_901_);
    leanh::lean_ctor_set(v___x_902_, 1, v___x_900_);
    leanh::lean_ctor_set(v___x_902_, 2, v___x_899_);
    return v___x_902_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49()
-> *mut leanh::LeanObject {
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48,
    );
    v___x_904_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18,
    );
    v___x_905_ = lean_array_push(v___x_904_, v___x_903_);
    return v___x_905_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50()
-> *mut leanh::LeanObject {
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49,
    );
    v___x_907_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16;
    v___x_908_ = leanh::lean_box(2);
    v___x_909_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_909_, 0, v___x_908_);
    leanh::lean_ctor_set(v___x_909_, 1, v___x_907_);
    leanh::lean_ctor_set(v___x_909_, 2, v___x_906_);
    return v___x_909_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50,
    );
    v___x_911_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13,
    );
    v___x_912_ = lean_array_push(v___x_911_, v___x_910_);
    return v___x_912_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52()
-> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51,
    );
    v___x_914_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11;
    v___x_915_ = leanh::lean_box(2);
    v___x_916_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_916_, 0, v___x_915_);
    leanh::lean_ctor_set(v___x_916_, 1, v___x_914_);
    leanh::lean_ctor_set(v___x_916_, 2, v___x_913_);
    return v___x_916_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53()
-> *mut leanh::LeanObject {
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_917_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52,
    );
    v___x_918_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_919_ = lean_array_push(v___x_918_, v___x_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54()
-> *mut leanh::LeanObject {
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_920_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53,
    );
    v___x_921_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9;
    v___x_922_ = leanh::lean_box(2);
    v___x_923_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
    leanh::lean_ctor_set(v___x_923_, 1, v___x_921_);
    leanh::lean_ctor_set(v___x_923_, 2, v___x_920_);
    return v___x_923_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55()
-> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54,
    );
    v___x_925_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_926_ = lean_array_push(v___x_925_, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56()
-> *mut leanh::LeanObject {
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55,
    );
    v___x_928_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7;
    v___x_929_ = leanh::lean_box(2);
    v___x_930_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_930_, 0, v___x_929_);
    leanh::lean_ctor_set(v___x_930_, 1, v___x_928_);
    leanh::lean_ctor_set(v___x_930_, 2, v___x_927_);
    return v___x_930_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57()
-> *mut leanh::LeanObject {
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56,
    );
    v___x_932_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_933_ = lean_array_push(v___x_932_, v___x_931_);
    return v___x_933_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58()
-> *mut leanh::LeanObject {
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57,
    );
    v___x_935_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4;
    v___x_936_ = leanh::lean_box(2);
    v___x_937_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_937_, 0, v___x_936_);
    leanh::lean_ctor_set(v___x_937_, 1, v___x_935_);
    leanh::lean_ctor_set(v___x_937_, 2, v___x_934_);
    return v___x_937_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1()
-> *mut leanh::LeanObject {
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58,
    );
    return v___x_938_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
    mut v_le_939_: *mut leanh::LeanObject,
    mut v_n_940_: *mut leanh::LeanObject,
    mut v_a_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_943_: u8 = 0;
    v_zero_942_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_943_ = lean_nat_dec_eq(v_n_940_, v_zero_942_);
    if v_isZero_943_ == 1 {
        leanh::lean_dec_ref(v_le_939_);
        return v_a_941_;
    } else {
        let mut v_one_944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_946_: u8 = 0;
        v_one_944_ = leanh::lean_unsigned_to_nat(1);
        v_n_945_ = lean_nat_sub(v_n_940_, v_one_944_);
        v_isZero_946_ = lean_nat_dec_eq(v_n_945_, v_zero_942_);
        if v_isZero_946_ == 1 {
            leanh::lean_dec(v_n_945_);
            leanh::lean_dec_ref(v_le_939_);
            return v_a_941_;
        } else {
            let mut v_n_947_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_951_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_952_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_947_ = lean_nat_sub(v_n_945_, v_one_944_);
            leanh::lean_dec(v_n_945_);
            v___x_948_ = leanh::lean_unsigned_to_nat(2);
            v___x_949_ = lean_nat_add(v_n_947_, v___x_948_);
            leanh::lean_dec(v_n_947_);
            v___x_950_ = l_List_MergeSort_Internal_splitInTwo___redArg(v___x_949_, v_a_941_);
            v_fst_951_ = leanh::lean_ctor_get(v___x_950_, 0);
            leanh::lean_inc(v_fst_951_);
            v_snd_952_ = leanh::lean_ctor_get(v___x_950_, 1);
            leanh::lean_inc(v_snd_952_);
            leanh::lean_dec_ref(v___x_950_);
            v___x_953_ = lean_nat_add(v___x_949_, v_one_944_);
            v___x_954_ = lean_nat_shiftr(v___x_953_, v_one_944_);
            leanh::lean_dec(v___x_953_);
            leanh::lean_inc_ref_n(v_le_939_, 2);
            v___x_955_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_939_, v___x_954_, v_fst_951_);
            leanh::lean_dec(v___x_954_);
            v___x_956_ = lean_nat_shiftr(v___x_949_, v_one_944_);
            leanh::lean_dec(v___x_949_);
            v___x_957_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_939_, v___x_956_, v_snd_952_);
            leanh::lean_dec(v___x_956_);
            v___x_958_ =
                l_List_MergeSort_Internal_mergeTR___redArg(v___x_955_, v___x_957_, v_le_939_);
            return v___x_958_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg___boxed(
    mut v_le_959_: *mut leanh::LeanObject,
    mut v_n_960_: *mut leanh::LeanObject,
    mut v_a_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
            v_le_959_, v_n_960_, v_a_961_,
        );
    leanh::lean_dec(v_n_960_);
    return v_res_962_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(
    mut v_00_u03b1_963_: *mut leanh::LeanObject,
    mut v_le_964_: *mut leanh::LeanObject,
    mut v_n_965_: *mut leanh::LeanObject,
    mut v_a_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
            v_le_964_, v_n_965_, v_a_966_,
        );
    return v___x_967_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___boxed(
    mut v_00_u03b1_968_: *mut leanh::LeanObject,
    mut v_le_969_: *mut leanh::LeanObject,
    mut v_n_970_: *mut leanh::LeanObject,
    mut v_a_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_972_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(
        v_00_u03b1_968_,
        v_le_969_,
        v_n_970_,
        v_a_971_,
    );
    leanh::lean_dec(v_n_970_);
    return v_res_972_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(
    mut v_x_973_: *mut leanh::LeanObject,
    mut v_x_974_: *mut leanh::LeanObject,
    mut v_h__1_975_: *mut leanh::LeanObject,
    mut v_h__2_976_: *mut leanh::LeanObject,
    mut v_h__3_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_979_: u8 = 0;
    v_zero_978_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_979_ = lean_nat_dec_eq(v_x_973_, v_zero_978_);
    if v_isZero_979_ == 1 {
        let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_977_);
        leanh::lean_dec(v_h__2_976_);
        leanh::lean_dec(v_x_974_);
        v___x_980_ = leanh::lean_apply_1(v_h__1_975_, leanh::lean_box(0));
        return v___x_980_;
    } else {
        let mut v_one_981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_983_: u8 = 0;
        leanh::lean_dec(v_h__1_975_);
        v_one_981_ = leanh::lean_unsigned_to_nat(1);
        v_n_982_ = lean_nat_sub(v_x_973_, v_one_981_);
        v_isZero_983_ = lean_nat_dec_eq(v_n_982_, v_zero_978_);
        if v_isZero_983_ == 1 {
            let mut v_head_984_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_n_982_);
            leanh::lean_dec(v_h__3_977_);
            v_head_984_ = leanh::lean_ctor_get(v_x_974_, 0);
            leanh::lean_inc(v_head_984_);
            leanh::lean_dec(v_x_974_);
            v___x_985_ =
                leanh::lean_apply_2(v_h__2_976_, v_head_984_, leanh::lean_box(0));
            return v___x_985_;
        } else {
            let mut v_n_986_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_976_);
            v_n_986_ = lean_nat_sub(v_n_982_, v_one_981_);
            leanh::lean_dec(v_n_982_);
            v___x_987_ = leanh::lean_apply_2(v_h__3_977_, v_n_986_, v_x_974_);
            return v___x_987_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg___boxed(
    mut v_x_988_: *mut leanh::LeanObject,
    mut v_x_989_: *mut leanh::LeanObject,
    mut v_h__1_990_: *mut leanh::LeanObject,
    mut v_h__2_991_: *mut leanh::LeanObject,
    mut v_h__3_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(v_x_988_, v_x_989_, v_h__1_990_, v_h__2_991_, v_h__3_992_);
    leanh::lean_dec(v_x_988_);
    return v_res_993_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(
    mut v_00_u03b1_994_: *mut leanh::LeanObject,
    mut v_motive_995_: *mut leanh::LeanObject,
    mut v_x_996_: *mut leanh::LeanObject,
    mut v_x_997_: *mut leanh::LeanObject,
    mut v_h__1_998_: *mut leanh::LeanObject,
    mut v_h__2_999_: *mut leanh::LeanObject,
    mut v_h__3_1000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1002_: u8 = 0;
    v_zero_1001_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1002_ = lean_nat_dec_eq(v_x_996_, v_zero_1001_);
    if v_isZero_1002_ == 1 {
        let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1000_);
        leanh::lean_dec(v_h__2_999_);
        leanh::lean_dec(v_x_997_);
        v___x_1003_ = leanh::lean_apply_1(v_h__1_998_, leanh::lean_box(0));
        return v___x_1003_;
    } else {
        let mut v_one_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1006_: u8 = 0;
        leanh::lean_dec(v_h__1_998_);
        v_one_1004_ = leanh::lean_unsigned_to_nat(1);
        v_n_1005_ = lean_nat_sub(v_x_996_, v_one_1004_);
        v_isZero_1006_ = lean_nat_dec_eq(v_n_1005_, v_zero_1001_);
        if v_isZero_1006_ == 1 {
            let mut v_head_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_n_1005_);
            leanh::lean_dec(v_h__3_1000_);
            v_head_1007_ = leanh::lean_ctor_get(v_x_997_, 0);
            leanh::lean_inc(v_head_1007_);
            leanh::lean_dec(v_x_997_);
            v___x_1008_ =
                leanh::lean_apply_2(v_h__2_999_, v_head_1007_, leanh::lean_box(0));
            return v___x_1008_;
        } else {
            let mut v_n_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_999_);
            v_n_1009_ = lean_nat_sub(v_n_1005_, v_one_1004_);
            leanh::lean_dec(v_n_1005_);
            v___x_1010_ = leanh::lean_apply_2(v_h__3_1000_, v_n_1009_, v_x_997_);
            return v___x_1010_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___boxed(
    mut v_00_u03b1_1011_: *mut leanh::LeanObject,
    mut v_motive_1012_: *mut leanh::LeanObject,
    mut v_x_1013_: *mut leanh::LeanObject,
    mut v_x_1014_: *mut leanh::LeanObject,
    mut v_h__1_1015_: *mut leanh::LeanObject,
    mut v_h__2_1016_: *mut leanh::LeanObject,
    mut v_h__3_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(v_00_u03b1_1011_, v_motive_1012_, v_x_1013_, v_x_1014_, v_h__1_1015_, v_h__2_1016_, v_h__3_1017_);
    leanh::lean_dec(v_x_1013_);
    return v_res_1018_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(
    mut v_x_1019_: *mut leanh::LeanObject,
    mut v_h__1_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1021_ = leanh::lean_ctor_get(v_x_1019_, 0);
    leanh::lean_inc(v_fst_1021_);
    v_snd_1022_ = leanh::lean_ctor_get(v_x_1019_, 1);
    leanh::lean_inc(v_snd_1022_);
    leanh::lean_dec_ref(v_x_1019_);
    v___x_1023_ = leanh::lean_apply_2(v_h__1_1020_, v_fst_1021_, v_snd_1022_);
    return v___x_1023_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(
    mut v_00_u03b1_1024_: *mut leanh::LeanObject,
    mut v_n_1025_: *mut leanh::LeanObject,
    mut v_motive_1026_: *mut leanh::LeanObject,
    mut v_x_1027_: *mut leanh::LeanObject,
    mut v_h__1_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1029_ = leanh::lean_ctor_get(v_x_1027_, 0);
    leanh::lean_inc(v_fst_1029_);
    v_snd_1030_ = leanh::lean_ctor_get(v_x_1027_, 1);
    leanh::lean_inc(v_snd_1030_);
    leanh::lean_dec_ref(v_x_1027_);
    v___x_1031_ = leanh::lean_apply_2(v_h__1_1028_, v_fst_1029_, v_snd_1030_);
    return v___x_1031_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___boxed(
    mut v_00_u03b1_1032_: *mut leanh::LeanObject,
    mut v_n_1033_: *mut leanh::LeanObject,
    mut v_motive_1034_: *mut leanh::LeanObject,
    mut v_x_1035_: *mut leanh::LeanObject,
    mut v_h__1_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1037_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(v_00_u03b1_1032_, v_n_1033_, v_motive_1034_, v_x_1035_, v_h__1_1036_);
    leanh::lean_dec(v_n_1033_);
    return v_res_1037_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR___redArg(
    mut v_l_1038_: *mut leanh::LeanObject,
    mut v_le_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_List_lengthTR___redArg(v_l_1038_);
    v___x_1041_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
            v_le_1039_,
            v___x_1040_,
            v_l_1038_,
        );
    leanh::lean_dec(v___x_1040_);
    return v___x_1041_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR(
    mut v_00_u03b1_1042_: *mut leanh::LeanObject,
    mut v_l_1043_: *mut leanh::LeanObject,
    mut v_le_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_List_MergeSort_Internal_mergeSortTR___redArg(v_l_1043_, v_le_1044_);
    return v___x_1045_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo___redArg(
    mut v_n_1046_: *mut leanh::LeanObject,
    mut v_l_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1048_ = leanh::lean_unsigned_to_nat(1);
                v___x_1049_ = lean_nat_add(v_n_1046_, v___x_1048_);
                v___x_1050_ = lean_nat_shiftr(v___x_1049_, v___x_1048_);
                leanh::lean_dec(v___x_1049_);
                v_r_1051_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_1050_, v_l_1047_);
                v_fst_1052_ = leanh::lean_ctor_get(v_r_1051_, 0);
                v_snd_1053_ = leanh::lean_ctor_get(v_r_1051_, 1);
                v_isSharedCheck_1060_ = (!leanh::lean_is_exclusive(v_r_1051_)) as u8;
                if v_isSharedCheck_1060_ == 0 {
                    v___x_1055_ = v_r_1051_;
                    v_isShared_1056_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1053_);
                    leanh::lean_inc(v_fst_1052_);
                    leanh::lean_dec(v_r_1051_);
                    v___x_1055_ = leanh::lean_box(0);
                    v_isShared_1056_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1056_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_fst_1052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1053_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo___redArg___boxed(
    mut v_n_1061_: *mut leanh::LeanObject,
    mut v_l_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_1061_, v_l_1062_);
    leanh::lean_dec(v_n_1061_);
    return v_res_1063_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo(
    mut v_00_u03b1_1064_: *mut leanh::LeanObject,
    mut v_n_1065_: *mut leanh::LeanObject,
    mut v_l_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_1065_, v_l_1066_);
    return v___x_1067_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo___boxed(
    mut v_00_u03b1_1068_: *mut leanh::LeanObject,
    mut v_n_1069_: *mut leanh::LeanObject,
    mut v_l_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_List_MergeSort_Internal_splitRevInTwo(v_00_u03b1_1068_, v_n_1069_, v_l_1070_);
    leanh::lean_dec(v_n_1069_);
    return v_res_1071_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(
    mut v_n_1072_: *mut leanh::LeanObject,
    mut v_l_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1074_ = leanh::lean_unsigned_to_nat(1);
                v___x_1075_ = lean_nat_shiftr(v_n_1072_, v___x_1074_);
                v_r_1076_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_1075_, v_l_1073_);
                v_fst_1077_ = leanh::lean_ctor_get(v_r_1076_, 0);
                v_snd_1078_ = leanh::lean_ctor_get(v_r_1076_, 1);
                v_isSharedCheck_1085_ = (!leanh::lean_is_exclusive(v_r_1076_)) as u8;
                if v_isSharedCheck_1085_ == 0 {
                    v___x_1080_ = v_r_1076_;
                    v_isShared_1081_ = v_isSharedCheck_1085_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1078_);
                    leanh::lean_inc(v_fst_1077_);
                    leanh::lean_dec(v_r_1076_);
                    v___x_1080_ = leanh::lean_box(0);
                    v_isShared_1081_ = v_isSharedCheck_1085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1081_ == 0 {
                    v___x_1083_ = v___x_1080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_fst_1077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_snd_1078_);
                    v___x_1083_ = v_reuseFailAlloc_1084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27___redArg___boxed(
    mut v_n_1086_: *mut leanh::LeanObject,
    mut v_l_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_1086_, v_l_1087_);
    leanh::lean_dec(v_n_1086_);
    return v_res_1088_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27(
    mut v_00_u03b1_1089_: *mut leanh::LeanObject,
    mut v_n_1090_: *mut leanh::LeanObject,
    mut v_l_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_1090_, v_l_1091_);
    return v___x_1092_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27___boxed(
    mut v_00_u03b1_1093_: *mut leanh::LeanObject,
    mut v_n_1094_: *mut leanh::LeanObject,
    mut v_l_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ =
        l_List_MergeSort_Internal_splitRevInTwo_x27(v_00_u03b1_1093_, v_n_1094_, v_l_1095_);
    leanh::lean_dec(v_n_1094_);
    return v_res_1096_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1()
-> *mut leanh::LeanObject {
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58,
    );
    return v___x_1097_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(
    mut v_le_1098_: *mut leanh::LeanObject,
    mut v_n_1099_: *mut leanh::LeanObject,
    mut v_a_1100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1102_: u8 = 0;
    v_zero_1101_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1102_ = lean_nat_dec_eq(v_n_1099_, v_zero_1101_);
    if v_isZero_1102_ == 1 {
        leanh::lean_dec_ref(v_le_1098_);
        return v_a_1100_;
    } else {
        let mut v_one_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1105_: u8 = 0;
        v_one_1103_ = leanh::lean_unsigned_to_nat(1);
        v_n_1104_ = lean_nat_sub(v_n_1099_, v_one_1103_);
        v_isZero_1105_ = lean_nat_dec_eq(v_n_1104_, v_zero_1101_);
        if v_isZero_1105_ == 1 {
            leanh::lean_dec(v_n_1104_);
            leanh::lean_dec_ref(v_le_1098_);
            return v_a_1100_;
        } else {
            let mut v_n_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_1106_ = lean_nat_sub(v_n_1104_, v_one_1103_);
            leanh::lean_dec(v_n_1104_);
            v___x_1107_ = leanh::lean_unsigned_to_nat(2);
            v___x_1108_ = lean_nat_add(v_n_1106_, v___x_1107_);
            leanh::lean_dec(v_n_1106_);
            v___x_1109_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v___x_1108_, v_a_1100_);
            v_fst_1110_ = leanh::lean_ctor_get(v___x_1109_, 0);
            leanh::lean_inc(v_fst_1110_);
            v_snd_1111_ = leanh::lean_ctor_get(v___x_1109_, 1);
            leanh::lean_inc(v_snd_1111_);
            leanh::lean_dec_ref(v___x_1109_);
            v___x_1112_ = lean_nat_add(v___x_1108_, v_one_1103_);
            v___x_1113_ = lean_nat_shiftr(v___x_1112_, v_one_1103_);
            leanh::lean_dec(v___x_1112_);
            leanh::lean_inc_ref_n(v_le_1098_, 2);
            v___x_1114_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1098_, v___x_1113_, v_fst_1110_);
            leanh::lean_dec(v___x_1113_);
            v___x_1115_ = lean_nat_shiftr(v___x_1108_, v_one_1103_);
            leanh::lean_dec(v___x_1108_);
            v___x_1116_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1098_, v___x_1115_, v_snd_1111_);
            leanh::lean_dec(v___x_1115_);
            v___x_1117_ =
                l_List_MergeSort_Internal_mergeTR___redArg(v___x_1114_, v___x_1116_, v_le_1098_);
            return v___x_1117_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(
    mut v_le_1118_: *mut leanh::LeanObject,
    mut v_n_1119_: *mut leanh::LeanObject,
    mut v_a_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1122_: u8 = 0;
    v_zero_1121_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1122_ = lean_nat_dec_eq(v_n_1119_, v_zero_1121_);
    if v_isZero_1122_ == 1 {
        leanh::lean_dec_ref(v_le_1118_);
        return v_a_1120_;
    } else {
        let mut v_one_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1125_: u8 = 0;
        v_one_1123_ = leanh::lean_unsigned_to_nat(1);
        v_n_1124_ = lean_nat_sub(v_n_1119_, v_one_1123_);
        v_isZero_1125_ = lean_nat_dec_eq(v_n_1124_, v_zero_1121_);
        if v_isZero_1125_ == 1 {
            leanh::lean_dec(v_n_1124_);
            leanh::lean_dec_ref(v_le_1118_);
            return v_a_1120_;
        } else {
            let mut v_n_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_1126_ = lean_nat_sub(v_n_1124_, v_one_1123_);
            leanh::lean_dec(v_n_1124_);
            v___x_1127_ = leanh::lean_unsigned_to_nat(2);
            v___x_1128_ = lean_nat_add(v_n_1126_, v___x_1127_);
            leanh::lean_dec(v_n_1126_);
            v___x_1129_ =
                l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v___x_1128_, v_a_1120_);
            v_fst_1130_ = leanh::lean_ctor_get(v___x_1129_, 0);
            leanh::lean_inc(v_fst_1130_);
            v_snd_1131_ = leanh::lean_ctor_get(v___x_1129_, 1);
            leanh::lean_inc(v_snd_1131_);
            leanh::lean_dec_ref(v___x_1129_);
            v___x_1132_ = lean_nat_add(v___x_1128_, v_one_1123_);
            v___x_1133_ = lean_nat_shiftr(v___x_1132_, v_one_1123_);
            leanh::lean_dec(v___x_1132_);
            leanh::lean_inc_ref_n(v_le_1118_, 2);
            v___x_1134_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1118_, v___x_1133_, v_snd_1131_);
            leanh::lean_dec(v___x_1133_);
            v___x_1135_ = lean_nat_shiftr(v___x_1128_, v_one_1123_);
            leanh::lean_dec(v___x_1128_);
            v___x_1136_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1118_, v___x_1135_, v_fst_1130_);
            leanh::lean_dec(v___x_1135_);
            v___x_1137_ =
                l_List_MergeSort_Internal_mergeTR___redArg(v___x_1134_, v___x_1136_, v_le_1118_);
            return v___x_1137_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg___boxed(
    mut v_le_1138_: *mut leanh::LeanObject,
    mut v_n_1139_: *mut leanh::LeanObject,
    mut v_a_1140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1141_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1138_, v_n_1139_, v_a_1140_);
    leanh::lean_dec(v_n_1139_);
    return v_res_1141_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg___boxed(
    mut v_le_1142_: *mut leanh::LeanObject,
    mut v_n_1143_: *mut leanh::LeanObject,
    mut v_a_1144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1142_, v_n_1143_, v_a_1144_);
    leanh::lean_dec(v_n_1143_);
    return v_res_1145_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(
    mut v_00_u03b1_1146_: *mut leanh::LeanObject,
    mut v_le_1147_: *mut leanh::LeanObject,
    mut v_n_1148_: *mut leanh::LeanObject,
    mut v_a_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1147_, v_n_1148_, v_a_1149_);
    return v___x_1150_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___boxed(
    mut v_00_u03b1_1151_: *mut leanh::LeanObject,
    mut v_le_1152_: *mut leanh::LeanObject,
    mut v_n_1153_: *mut leanh::LeanObject,
    mut v_a_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(
            v_00_u03b1_1151_,
            v_le_1152_,
            v_n_1153_,
            v_a_1154_,
        );
    leanh::lean_dec(v_n_1153_);
    return v_res_1155_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(
    mut v_00_u03b1_1156_: *mut leanh::LeanObject,
    mut v_le_1157_: *mut leanh::LeanObject,
    mut v_n_1158_: *mut leanh::LeanObject,
    mut v_a_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1157_, v_n_1158_, v_a_1159_);
    return v___x_1160_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___boxed(
    mut v_00_u03b1_1161_: *mut leanh::LeanObject,
    mut v_le_1162_: *mut leanh::LeanObject,
    mut v_n_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(
            v_00_u03b1_1161_,
            v_le_1162_,
            v_n_1163_,
            v_a_1164_,
        );
    leanh::lean_dec(v_n_1163_);
    return v_res_1165_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(
    mut v_x_1166_: *mut leanh::LeanObject,
    mut v_h__1_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1168_ = leanh::lean_ctor_get(v_x_1166_, 0);
    leanh::lean_inc(v_fst_1168_);
    v_snd_1169_ = leanh::lean_ctor_get(v_x_1166_, 1);
    leanh::lean_inc(v_snd_1169_);
    leanh::lean_dec_ref(v_x_1166_);
    v___x_1170_ = leanh::lean_apply_2(v_h__1_1167_, v_fst_1168_, v_snd_1169_);
    return v___x_1170_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(
    mut v_00_u03b1_1171_: *mut leanh::LeanObject,
    mut v_n_1172_: *mut leanh::LeanObject,
    mut v_motive_1173_: *mut leanh::LeanObject,
    mut v_x_1174_: *mut leanh::LeanObject,
    mut v_h__1_1175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1176_ = leanh::lean_ctor_get(v_x_1174_, 0);
    leanh::lean_inc(v_fst_1176_);
    v_snd_1177_ = leanh::lean_ctor_get(v_x_1174_, 1);
    leanh::lean_inc(v_snd_1177_);
    leanh::lean_dec_ref(v_x_1174_);
    v___x_1178_ = leanh::lean_apply_2(v_h__1_1175_, v_fst_1176_, v_snd_1177_);
    return v___x_1178_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___boxed(
    mut v_00_u03b1_1179_: *mut leanh::LeanObject,
    mut v_n_1180_: *mut leanh::LeanObject,
    mut v_motive_1181_: *mut leanh::LeanObject,
    mut v_x_1182_: *mut leanh::LeanObject,
    mut v_h__1_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1184_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(v_00_u03b1_1179_, v_n_1180_, v_motive_1181_, v_x_1182_, v_h__1_1183_);
    leanh::lean_dec(v_n_1180_);
    return v_res_1184_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(
    mut v_l_1185_: *mut leanh::LeanObject,
    mut v_le_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_List_lengthTR___redArg(v_l_1185_);
    v___x_1188_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1186_, v___x_1187_, v_l_1185_);
    leanh::lean_dec(v___x_1187_);
    return v___x_1188_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR_u2082(
    mut v_00_u03b1_1189_: *mut leanh::LeanObject,
    mut v_l_1190_: *mut leanh::LeanObject,
    mut v_le_1191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v_l_1190_, v_le_1191_);
    return v___x_1192_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_1193_: *mut leanh::LeanObject,
    mut v_x_1194_: *mut leanh::LeanObject,
    mut v_h__1_1195_: *mut leanh::LeanObject,
    mut v_h__2_1196_: *mut leanh::LeanObject,
    mut v_h__3_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1193_) == 0 {
        let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1197_);
        leanh::lean_dec(v_h__2_1196_);
        v___x_1198_ = leanh::lean_apply_1(v_h__1_1195_, v_x_1194_);
        return v___x_1198_;
    } else {
        let mut v_tail_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1195_);
        v_tail_1199_ = leanh::lean_ctor_get(v_x_1193_, 1);
        if leanh::lean_obj_tag(v_tail_1199_) == 0 {
            let mut v_head_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1197_);
            v_head_1200_ = leanh::lean_ctor_get(v_x_1193_, 0);
            leanh::lean_inc(v_head_1200_);
            leanh::lean_dec_ref_known(v_x_1193_, 2);
            v___x_1201_ = leanh::lean_apply_2(v_h__2_1196_, v_head_1200_, v_x_1194_);
            return v___x_1201_;
        } else {
            let mut v_head_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_1199_);
            leanh::lean_dec(v_h__2_1196_);
            v_head_1202_ = leanh::lean_ctor_get(v_x_1193_, 0);
            leanh::lean_inc(v_head_1202_);
            leanh::lean_dec_ref_known(v_x_1193_, 2);
            v_head_1203_ = leanh::lean_ctor_get(v_tail_1199_, 0);
            leanh::lean_inc(v_head_1203_);
            v_tail_1204_ = leanh::lean_ctor_get(v_tail_1199_, 1);
            leanh::lean_inc(v_tail_1204_);
            leanh::lean_dec_ref_known(v_tail_1199_, 2);
            v___x_1205_ = leanh::lean_apply_4(
                v_h__3_1197_,
                v_head_1202_,
                v_head_1203_,
                v_tail_1204_,
                v_x_1194_,
            );
            return v___x_1205_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_1206_: *mut leanh::LeanObject,
    mut v_motive_1207_: *mut leanh::LeanObject,
    mut v_x_1208_: *mut leanh::LeanObject,
    mut v_x_1209_: *mut leanh::LeanObject,
    mut v_h__1_1210_: *mut leanh::LeanObject,
    mut v_h__2_1211_: *mut leanh::LeanObject,
    mut v_h__3_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1208_) == 0 {
        let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1212_);
        leanh::lean_dec(v_h__2_1211_);
        v___x_1213_ = leanh::lean_apply_1(v_h__1_1210_, v_x_1209_);
        return v___x_1213_;
    } else {
        let mut v_tail_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1210_);
        v_tail_1214_ = leanh::lean_ctor_get(v_x_1208_, 1);
        if leanh::lean_obj_tag(v_tail_1214_) == 0 {
            let mut v_head_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1212_);
            v_head_1215_ = leanh::lean_ctor_get(v_x_1208_, 0);
            leanh::lean_inc(v_head_1215_);
            leanh::lean_dec_ref_known(v_x_1208_, 2);
            v___x_1216_ = leanh::lean_apply_2(v_h__2_1211_, v_head_1215_, v_x_1209_);
            return v___x_1216_;
        } else {
            let mut v_head_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_1214_);
            leanh::lean_dec(v_h__2_1211_);
            v_head_1217_ = leanh::lean_ctor_get(v_x_1208_, 0);
            leanh::lean_inc(v_head_1217_);
            leanh::lean_dec_ref_known(v_x_1208_, 2);
            v_head_1218_ = leanh::lean_ctor_get(v_tail_1214_, 0);
            leanh::lean_inc(v_head_1218_);
            v_tail_1219_ = leanh::lean_ctor_get(v_tail_1214_, 1);
            leanh::lean_inc(v_tail_1219_);
            leanh::lean_dec_ref_known(v_tail_1214_, 2);
            v___x_1220_ = leanh::lean_apply_4(
                v_h__3_1212_,
                v_head_1217_,
                v_head_1218_,
                v_tail_1219_,
                v_x_1209_,
            );
            return v___x_1220_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Sort_Impl(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Sort_Impl(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_MergeSort_Internal_mergeSortTR___auto__1 =
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1();
    leanh::lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1);
    l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1 =
        _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1();
    leanh::lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Sort_Impl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Sort_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Sort_Impl(builtin);
}