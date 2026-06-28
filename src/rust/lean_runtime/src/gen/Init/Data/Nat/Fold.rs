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
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value:
    LeanStringObject<10> = LeanStringObject {
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value)
        as *mut LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_0:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value
        ) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value:
    LeanStringObject<19> = LeanStringObject {
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value)
        as *mut LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_0:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value
        ) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value:
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
    m_data: [111, 109, 101, 103, 97, 0],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value
)
    as *mut LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_0:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value
        ) as *mut LeanObject,
        14893461734720614794 as *mut LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value
)
    as *mut LeanObject;
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value
)
    as *mut LeanObject;
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_0:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_1:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_2:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value:
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
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value
        ) as *mut LeanObject,
        3488656302031949961 as *mut LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value
)
    as *mut LeanObject;
pub static l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16: *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16_value
)
    as *mut LeanObject;
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_dfold___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfoldRev___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold__zero___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_dfold__succ___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold__congr___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfold__add___auto__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__zero___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__succ___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__congr___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_dfoldRev__add___auto__5: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Nat_fold___redArg___lam__0(
    mut v_x_642_: *mut LeanObject,
    mut v_i_643_: *mut LeanObject,
    mut v_h_644_: *mut LeanObject,
    mut v___y_645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    v___x_646_ = lean_apply_3(v_x_642_, v_i_643_, lean_box(0), v___y_645_);
    return v___x_646_;
}
pub unsafe fn l_Nat_fold___redArg(
    mut v_x_647_: *mut LeanObject,
    mut v_x_648_: *mut LeanObject,
    mut v_x_649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_651_: u8 = 0;
    v_zero_650_ = lean_unsigned_to_nat(0);
    v_isZero_651_ = lean_nat_dec_eq(v_x_647_, v_zero_650_);
    if v_isZero_651_ == 1 {
        lean_dec(v_x_648_);
        lean_inc(v_x_649_);
        return v_x_649_;
    } else {
        let mut v___f_652_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_653_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_x_648_);
        v___f_652_ =
            lean_alloc_closure(l_Nat_fold___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
        lean_closure_set(v___f_652_, 0, v_x_648_);
        v_one_653_ = lean_unsigned_to_nat(1);
        v_n_654_ = lean_nat_sub(v_x_647_, v_one_653_);
        v___x_655_ = l_Nat_fold___redArg(v_n_654_, v___f_652_, v_x_649_);
        v___x_656_ = lean_apply_3(v_x_648_, v_n_654_, lean_box(0), v___x_655_);
        return v___x_656_;
    }
}
pub unsafe fn l_Nat_fold___redArg___boxed(
    mut v_x_657_: *mut LeanObject,
    mut v_x_658_: *mut LeanObject,
    mut v_x_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_660_: *mut LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Nat_fold___redArg(v_x_657_, v_x_658_, v_x_659_);
    lean_dec(v_x_659_);
    lean_dec(v_x_657_);
    return v_res_660_;
}
pub unsafe fn l_Nat_fold(
    mut v_00_u03b1_661_: *mut LeanObject,
    mut v_x_662_: *mut LeanObject,
    mut v_x_663_: *mut LeanObject,
    mut v_x_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Nat_fold___redArg(v_x_662_, v_x_663_, v_x_664_);
    return v___x_665_;
}
pub unsafe fn l_Nat_fold___boxed(
    mut v_00_u03b1_666_: *mut LeanObject,
    mut v_x_667_: *mut LeanObject,
    mut v_x_668_: *mut LeanObject,
    mut v_x_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_670_: *mut LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Nat_fold(v_00_u03b1_666_, v_x_667_, v_x_668_, v_x_669_);
    lean_dec(v_x_669_);
    lean_dec(v_x_667_);
    return v_res_670_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
    mut v_n_671_: *mut LeanObject,
    mut v_f_672_: *mut LeanObject,
    mut v_j_673_: *mut LeanObject,
    mut v_a_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_676_: u8 = 0;
    let mut v_one_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_675_ = lean_unsigned_to_nat(0);
                v_isZero_676_ = lean_nat_dec_eq(v_j_673_, v_zero_675_);
                if v_isZero_676_ == 1 {
                    lean_dec(v_j_673_);
                    lean_dec(v_f_672_);
                    return v_a_674_;
                } else {
                    v_one_677_ = lean_unsigned_to_nat(1);
                    v_n_678_ = lean_nat_sub(v_j_673_, v_one_677_);
                    v___x_679_ = lean_nat_sub(v_n_671_, v_j_673_);
                    lean_dec(v_j_673_);
                    lean_inc(v_f_672_);
                    v___x_680_ = lean_apply_3(v_f_672_, v___x_679_, lean_box(0), v_a_674_);
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
    mut v_n_682_: *mut LeanObject,
    mut v_f_683_: *mut LeanObject,
    mut v_j_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_686_: *mut LeanObject = core::ptr::null_mut();
    v_res_686_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_682_, v_f_683_, v_j_684_, v_a_685_,
    );
    lean_dec(v_n_682_);
    return v_res_686_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(
    mut v_00_u03b1_687_: *mut LeanObject,
    mut v_n_688_: *mut LeanObject,
    mut v_f_689_: *mut LeanObject,
    mut v_j_690_: *mut LeanObject,
    mut v_a_691_: *mut LeanObject,
    mut v_a_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    v___x_693_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_688_, v_f_689_, v_j_690_, v_a_692_,
    );
    return v___x_693_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___boxed(
    mut v_00_u03b1_694_: *mut LeanObject,
    mut v_n_695_: *mut LeanObject,
    mut v_f_696_: *mut LeanObject,
    mut v_j_697_: *mut LeanObject,
    mut v_a_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_700_: *mut LeanObject = core::ptr::null_mut();
    v_res_700_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(
        v_00_u03b1_694_,
        v_n_695_,
        v_f_696_,
        v_j_697_,
        v_a_698_,
        v_a_699_,
    );
    lean_dec(v_n_695_);
    return v_res_700_;
}
pub unsafe fn l_Nat_foldTR___redArg(
    mut v_n_701_: *mut LeanObject,
    mut v_f_702_: *mut LeanObject,
    mut v_init_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_701_);
    v___x_704_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_701_,
        v_f_702_,
        v_n_701_,
        v_init_703_,
    );
    lean_dec(v_n_701_);
    return v___x_704_;
}
pub unsafe fn l_Nat_foldTR(
    mut v_00_u03b1_705_: *mut LeanObject,
    mut v_n_706_: *mut LeanObject,
    mut v_f_707_: *mut LeanObject,
    mut v_init_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_706_);
    v___x_709_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v_n_706_,
        v_f_707_,
        v_n_706_,
        v_init_708_,
    );
    lean_dec(v_n_706_);
    return v___x_709_;
}
pub unsafe fn l_Nat_foldRev___redArg(
    mut v_x_710_: *mut LeanObject,
    mut v_x_711_: *mut LeanObject,
    mut v_x_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_714_: u8 = 0;
    let mut v___f_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_713_ = lean_unsigned_to_nat(0);
                v_isZero_714_ = lean_nat_dec_eq(v_x_710_, v_zero_713_);
                if v_isZero_714_ == 1 {
                    lean_dec(v_x_711_);
                    lean_dec(v_x_710_);
                    return v_x_712_;
                } else {
                    lean_inc(v_x_711_);
                    v___f_715_ = lean_alloc_closure(
                        l_Nat_fold___redArg___lam__0 as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    lean_closure_set(v___f_715_, 0, v_x_711_);
                    v_one_716_ = lean_unsigned_to_nat(1);
                    v_n_717_ = lean_nat_sub(v_x_710_, v_one_716_);
                    lean_dec(v_x_710_);
                    lean_inc(v_n_717_);
                    v___x_718_ = lean_apply_3(v_x_711_, v_n_717_, lean_box(0), v_x_712_);
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
    mut v_00_u03b1_720_: *mut LeanObject,
    mut v_x_721_: *mut LeanObject,
    mut v_x_722_: *mut LeanObject,
    mut v_x_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Nat_foldRev___redArg(v_x_721_, v_x_722_, v_x_723_);
    return v___x_724_;
}
pub unsafe fn l_Nat_any___lam__0(
    mut v_x_725_: *mut LeanObject,
    mut v_i_726_: *mut LeanObject,
    mut v_h_727_: *mut LeanObject,
) -> u8 {
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: u8 = 0;
    v___x_728_ = lean_apply_2(v_x_725_, v_i_726_, lean_box(0));
    v___x_729_ = (lean_unbox(v___x_728_) as u8);
    return v___x_729_;
}
pub unsafe fn l_Nat_any___lam__0___boxed(
    mut v_x_730_: *mut LeanObject,
    mut v_i_731_: *mut LeanObject,
    mut v_h_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_733_: u8 = 0;
    let mut v_r_734_: *mut LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Nat_any___lam__0(v_x_730_, v_i_731_, v_h_732_);
    v_r_734_ = lean_box((v_res_733_) as usize);
    return v_r_734_;
}
pub unsafe fn l_Nat_any(mut v_x_735_: *mut LeanObject, mut v_x_736_: *mut LeanObject) -> u8 {
    let mut v_zero_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_738_: u8 = 0;
    v_zero_737_ = lean_unsigned_to_nat(0);
    v_isZero_738_ = lean_nat_dec_eq(v_x_735_, v_zero_737_);
    if v_isZero_738_ == 1 {
        let mut v___x_739_: u8 = 0;
        lean_dec_ref(v_x_736_);
        v___x_739_ = 0;
        return v___x_739_;
    } else {
        let mut v___f_740_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_741_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_743_: u8 = 0;
        lean_inc_ref(v_x_736_);
        v___f_740_ = lean_alloc_closure(l_Nat_any___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
        lean_closure_set(v___f_740_, 0, v_x_736_);
        v_one_741_ = lean_unsigned_to_nat(1);
        v_n_742_ = lean_nat_sub(v_x_735_, v_one_741_);
        v___x_743_ = l_Nat_any(v_n_742_, v___f_740_);
        if v___x_743_ == 0 {
            let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_745_: u8 = 0;
            v___x_744_ = lean_apply_2(v_x_736_, v_n_742_, lean_box(0));
            v___x_745_ = (lean_unbox(v___x_744_) as u8);
            return v___x_745_;
        } else {
            lean_dec(v_n_742_);
            lean_dec_ref(v_x_736_);
            return v___x_743_;
        }
    }
}
pub unsafe fn l_Nat_any___boxed(
    mut v_x_746_: *mut LeanObject,
    mut v_x_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_748_: u8 = 0;
    let mut v_r_749_: *mut LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Nat_any(v_x_746_, v_x_747_);
    lean_dec(v_x_746_);
    v_r_749_ = lean_box((v_res_748_) as usize);
    return v_r_749_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(
    mut v_n_750_: *mut LeanObject,
    mut v_f_751_: *mut LeanObject,
    mut v_i_752_: *mut LeanObject,
) -> u8 {
    let mut v_zero_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_754_: u8 = 0;
    let mut v___x_755_: u8 = 0;
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    let mut v_one_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_753_ = lean_unsigned_to_nat(0);
                v_isZero_754_ = lean_nat_dec_eq(v_i_752_, v_zero_753_);
                if v_isZero_754_ == 1 {
                    lean_dec(v_i_752_);
                    lean_dec_ref(v_f_751_);
                    v___x_755_ = 0;
                    return v___x_755_;
                } else {
                    v___x_756_ = lean_nat_sub(v_n_750_, v_i_752_);
                    lean_inc_ref(v_f_751_);
                    v___x_757_ = lean_apply_2(v_f_751_, v___x_756_, lean_box(0));
                    v___x_758_ = (lean_unbox(v___x_757_) as u8);
                    if v___x_758_ == 0 {
                        v_one_759_ = lean_unsigned_to_nat(1);
                        v_n_760_ = lean_nat_sub(v_i_752_, v_one_759_);
                        lean_dec(v_i_752_);
                        v_i_752_ = v_n_760_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_752_);
                        lean_dec_ref(v_f_751_);
                        v___x_762_ = (lean_unbox(v___x_757_) as u8);
                        return v___x_762_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg___boxed(
    mut v_n_763_: *mut LeanObject,
    mut v_f_764_: *mut LeanObject,
    mut v_i_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_766_: u8 = 0;
    let mut v_r_767_: *mut LeanObject = core::ptr::null_mut();
    v_res_766_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_763_, v_f_764_, v_i_765_);
    lean_dec(v_n_763_);
    v_r_767_ = lean_box((v_res_766_) as usize);
    return v_r_767_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(
    mut v_n_768_: *mut LeanObject,
    mut v_f_769_: *mut LeanObject,
    mut v_i_770_: *mut LeanObject,
    mut v_a_771_: *mut LeanObject,
) -> u8 {
    let mut v___x_772_: u8 = 0;
    v___x_772_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_768_, v_f_769_, v_i_770_);
    return v___x_772_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___boxed(
    mut v_n_773_: *mut LeanObject,
    mut v_f_774_: *mut LeanObject,
    mut v_i_775_: *mut LeanObject,
    mut v_a_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_777_: u8 = 0;
    let mut v_r_778_: *mut LeanObject = core::ptr::null_mut();
    v_res_777_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(v_n_773_, v_f_774_, v_i_775_, v_a_776_);
    lean_dec(v_n_773_);
    v_r_778_ = lean_box((v_res_777_) as usize);
    return v_r_778_;
}
pub unsafe fn l_Nat_anyTR(mut v_n_779_: *mut LeanObject, mut v_f_780_: *mut LeanObject) -> u8 {
    let mut v___x_781_: u8 = 0;
    lean_inc(v_n_779_);
    v___x_781_ =
        l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_779_, v_f_780_, v_n_779_);
    lean_dec(v_n_779_);
    return v___x_781_;
}
pub unsafe fn l_Nat_anyTR___boxed(
    mut v_n_782_: *mut LeanObject,
    mut v_f_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_784_: u8 = 0;
    let mut v_r_785_: *mut LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Nat_anyTR(v_n_782_, v_f_783_);
    v_r_785_ = lean_box((v_res_784_) as usize);
    return v_r_785_;
}
pub unsafe fn l_Nat_all(mut v_x_786_: *mut LeanObject, mut v_x_787_: *mut LeanObject) -> u8 {
    let mut v_zero_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_789_: u8 = 0;
    v_zero_788_ = lean_unsigned_to_nat(0);
    v_isZero_789_ = lean_nat_dec_eq(v_x_786_, v_zero_788_);
    if v_isZero_789_ == 1 {
        lean_dec_ref(v_x_787_);
        return v_isZero_789_;
    } else {
        let mut v___f_790_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_791_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_793_: u8 = 0;
        lean_inc_ref(v_x_787_);
        v___f_790_ = lean_alloc_closure(l_Nat_any___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
        lean_closure_set(v___f_790_, 0, v_x_787_);
        v_one_791_ = lean_unsigned_to_nat(1);
        v_n_792_ = lean_nat_sub(v_x_786_, v_one_791_);
        v___x_793_ = l_Nat_all(v_n_792_, v___f_790_);
        if v___x_793_ == 0 {
            lean_dec(v_n_792_);
            lean_dec_ref(v_x_787_);
            return v___x_793_;
        } else {
            let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_795_: u8 = 0;
            v___x_794_ = lean_apply_2(v_x_787_, v_n_792_, lean_box(0));
            v___x_795_ = (lean_unbox(v___x_794_) as u8);
            return v___x_795_;
        }
    }
}
pub unsafe fn l_Nat_all___boxed(
    mut v_x_796_: *mut LeanObject,
    mut v_x_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_798_: u8 = 0;
    let mut v_r_799_: *mut LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Nat_all(v_x_796_, v_x_797_);
    lean_dec(v_x_796_);
    v_r_799_ = lean_box((v_res_798_) as usize);
    return v_r_799_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(
    mut v_n_800_: *mut LeanObject,
    mut v_f_801_: *mut LeanObject,
    mut v_i_802_: *mut LeanObject,
) -> u8 {
    let mut v_zero_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_804_: u8 = 0;
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: u8 = 0;
    let mut v_one_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_810_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_803_ = lean_unsigned_to_nat(0);
                v_isZero_804_ = lean_nat_dec_eq(v_i_802_, v_zero_803_);
                if v_isZero_804_ == 1 {
                    lean_dec(v_i_802_);
                    lean_dec_ref(v_f_801_);
                    return v_isZero_804_;
                } else {
                    v___x_805_ = lean_nat_sub(v_n_800_, v_i_802_);
                    lean_inc_ref(v_f_801_);
                    v___x_806_ = lean_apply_2(v_f_801_, v___x_805_, lean_box(0));
                    v___x_807_ = (lean_unbox(v___x_806_) as u8);
                    if v___x_807_ == 0 {
                        lean_dec(v_i_802_);
                        lean_dec_ref(v_f_801_);
                        v___x_808_ = (lean_unbox(v___x_806_) as u8);
                        return v___x_808_;
                    } else {
                        v_one_809_ = lean_unsigned_to_nat(1);
                        v_n_810_ = lean_nat_sub(v_i_802_, v_one_809_);
                        lean_dec(v_i_802_);
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
    mut v_n_812_: *mut LeanObject,
    mut v_f_813_: *mut LeanObject,
    mut v_i_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_815_: u8 = 0;
    let mut v_r_816_: *mut LeanObject = core::ptr::null_mut();
    v_res_815_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_812_, v_f_813_, v_i_814_);
    lean_dec(v_n_812_);
    v_r_816_ = lean_box((v_res_815_) as usize);
    return v_r_816_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(
    mut v_n_817_: *mut LeanObject,
    mut v_f_818_: *mut LeanObject,
    mut v_i_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
) -> u8 {
    let mut v___x_821_: u8 = 0;
    v___x_821_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_817_, v_f_818_, v_i_819_);
    return v___x_821_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___boxed(
    mut v_n_822_: *mut LeanObject,
    mut v_f_823_: *mut LeanObject,
    mut v_i_824_: *mut LeanObject,
    mut v_a_825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_826_: u8 = 0;
    let mut v_r_827_: *mut LeanObject = core::ptr::null_mut();
    v_res_826_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(v_n_822_, v_f_823_, v_i_824_, v_a_825_);
    lean_dec(v_n_822_);
    v_r_827_ = lean_box((v_res_826_) as usize);
    return v_r_827_;
}
pub unsafe fn l_Nat_allTR(mut v_n_828_: *mut LeanObject, mut v_f_829_: *mut LeanObject) -> u8 {
    let mut v___x_830_: u8 = 0;
    lean_inc(v_n_828_);
    v___x_830_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_828_, v_f_829_, v_n_828_);
    lean_dec(v_n_828_);
    return v___x_830_;
}
pub unsafe fn l_Nat_allTR___boxed(
    mut v_n_831_: *mut LeanObject,
    mut v_f_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_833_: u8 = 0;
    let mut v_r_834_: *mut LeanObject = core::ptr::null_mut();
    v_res_833_ = l_Nat_allTR(v_n_831_, v_f_832_);
    v_r_834_ = lean_box((v_res_833_) as usize);
    return v_r_834_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(
    mut v_x_835_: *mut LeanObject,
    mut v_x_836_: *mut LeanObject,
    mut v_h__1_837_: *mut LeanObject,
    mut v_h__2_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_840_: u8 = 0;
    v_zero_839_ = lean_unsigned_to_nat(0);
    v_isZero_840_ = lean_nat_dec_eq(v_x_835_, v_zero_839_);
    if v_isZero_840_ == 1 {
        let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_838_);
        v___x_841_ = lean_apply_2(v_h__1_837_, lean_box(0), v_x_836_);
        return v___x_841_;
    } else {
        let mut v_one_842_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_837_);
        v_one_842_ = lean_unsigned_to_nat(1);
        v_n_843_ = lean_nat_sub(v_x_835_, v_one_842_);
        v___x_844_ = lean_apply_3(v_h__2_838_, v_n_843_, lean_box(0), v_x_836_);
        return v___x_844_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg___boxed(
    mut v_x_845_: *mut LeanObject,
    mut v_x_846_: *mut LeanObject,
    mut v_h__1_847_: *mut LeanObject,
    mut v_h__2_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_849_: *mut LeanObject = core::ptr::null_mut();
    v_res_849_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(
        v_x_845_,
        v_x_846_,
        v_h__1_847_,
        v_h__2_848_,
    );
    lean_dec(v_x_845_);
    return v_res_849_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(
    mut v_00_u03b1_850_: *mut LeanObject,
    mut v_n_851_: *mut LeanObject,
    mut v_motive_852_: *mut LeanObject,
    mut v_x_853_: *mut LeanObject,
    mut v_x_854_: *mut LeanObject,
    mut v_x_855_: *mut LeanObject,
    mut v_h__1_856_: *mut LeanObject,
    mut v_h__2_857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_859_: u8 = 0;
    v_zero_858_ = lean_unsigned_to_nat(0);
    v_isZero_859_ = lean_nat_dec_eq(v_x_853_, v_zero_858_);
    if v_isZero_859_ == 1 {
        let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_857_);
        v___x_860_ = lean_apply_2(v_h__1_856_, lean_box(0), v_x_855_);
        return v___x_860_;
    } else {
        let mut v_one_861_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_856_);
        v_one_861_ = lean_unsigned_to_nat(1);
        v_n_862_ = lean_nat_sub(v_x_853_, v_one_861_);
        v___x_863_ = lean_apply_3(v_h__2_857_, v_n_862_, lean_box(0), v_x_855_);
        return v___x_863_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___boxed(
    mut v_00_u03b1_864_: *mut LeanObject,
    mut v_n_865_: *mut LeanObject,
    mut v_motive_866_: *mut LeanObject,
    mut v_x_867_: *mut LeanObject,
    mut v_x_868_: *mut LeanObject,
    mut v_x_869_: *mut LeanObject,
    mut v_h__1_870_: *mut LeanObject,
    mut v_h__2_871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_872_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x_867_);
    lean_dec(v_n_865_);
    return v_res_872_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(
    mut v_x_873_: *mut LeanObject,
    mut v_x_874_: *mut LeanObject,
    mut v_x_875_: *mut LeanObject,
    mut v_h__1_876_: *mut LeanObject,
    mut v_h__2_877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_879_: u8 = 0;
    v_zero_878_ = lean_unsigned_to_nat(0);
    v_isZero_879_ = lean_nat_dec_eq(v_x_873_, v_zero_878_);
    if v_isZero_879_ == 1 {
        let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_877_);
        v___x_880_ = lean_apply_2(v_h__1_876_, v_x_874_, v_x_875_);
        return v___x_880_;
    } else {
        let mut v_one_881_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_876_);
        v_one_881_ = lean_unsigned_to_nat(1);
        v_n_882_ = lean_nat_sub(v_x_873_, v_one_881_);
        v___x_883_ = lean_apply_3(v_h__2_877_, v_n_882_, v_x_874_, v_x_875_);
        return v___x_883_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg___boxed(
    mut v_x_884_: *mut LeanObject,
    mut v_x_885_: *mut LeanObject,
    mut v_x_886_: *mut LeanObject,
    mut v_h__1_887_: *mut LeanObject,
    mut v_h__2_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_889_: *mut LeanObject = core::ptr::null_mut();
    v_res_889_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(
        v_x_884_,
        v_x_885_,
        v_x_886_,
        v_h__1_887_,
        v_h__2_888_,
    );
    lean_dec(v_x_884_);
    return v_res_889_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(
    mut v_00_u03b1_890_: *mut LeanObject,
    mut v_motive_891_: *mut LeanObject,
    mut v_x_892_: *mut LeanObject,
    mut v_x_893_: *mut LeanObject,
    mut v_x_894_: *mut LeanObject,
    mut v_h__1_895_: *mut LeanObject,
    mut v_h__2_896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_898_: u8 = 0;
    v_zero_897_ = lean_unsigned_to_nat(0);
    v_isZero_898_ = lean_nat_dec_eq(v_x_892_, v_zero_897_);
    if v_isZero_898_ == 1 {
        let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_896_);
        v___x_899_ = lean_apply_2(v_h__1_895_, v_x_893_, v_x_894_);
        return v___x_899_;
    } else {
        let mut v_one_900_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_895_);
        v_one_900_ = lean_unsigned_to_nat(1);
        v_n_901_ = lean_nat_sub(v_x_892_, v_one_900_);
        v___x_902_ = lean_apply_3(v_h__2_896_, v_n_901_, v_x_893_, v_x_894_);
        return v___x_902_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___boxed(
    mut v_00_u03b1_903_: *mut LeanObject,
    mut v_motive_904_: *mut LeanObject,
    mut v_x_905_: *mut LeanObject,
    mut v_x_906_: *mut LeanObject,
    mut v_x_907_: *mut LeanObject,
    mut v_h__1_908_: *mut LeanObject,
    mut v_h__2_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_910_: *mut LeanObject = core::ptr::null_mut();
    v_res_910_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(
        v_00_u03b1_903_,
        v_motive_904_,
        v_x_905_,
        v_x_906_,
        v_x_907_,
        v_h__1_908_,
        v_h__2_909_,
    );
    lean_dec(v_x_905_);
    return v_res_910_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(
    mut v_x_911_: *mut LeanObject,
    mut v_h__1_912_: *mut LeanObject,
    mut v_h__2_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_915_: u8 = 0;
    v_zero_914_ = lean_unsigned_to_nat(0);
    v_isZero_915_ = lean_nat_dec_eq(v_x_911_, v_zero_914_);
    if v_isZero_915_ == 1 {
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_913_);
        v___x_916_ = lean_apply_1(v_h__1_912_, lean_box(0));
        return v___x_916_;
    } else {
        let mut v_one_917_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_912_);
        v_one_917_ = lean_unsigned_to_nat(1);
        v_n_918_ = lean_nat_sub(v_x_911_, v_one_917_);
        v___x_919_ = lean_apply_2(v_h__2_913_, v_n_918_, lean_box(0));
        return v___x_919_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg___boxed(
    mut v_x_920_: *mut LeanObject,
    mut v_h__1_921_: *mut LeanObject,
    mut v_h__2_922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_923_: *mut LeanObject = core::ptr::null_mut();
    v_res_923_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(
        v_x_920_,
        v_h__1_921_,
        v_h__2_922_,
    );
    lean_dec(v_x_920_);
    return v_res_923_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(
    mut v_n_924_: *mut LeanObject,
    mut v_motive_925_: *mut LeanObject,
    mut v_x_926_: *mut LeanObject,
    mut v_x_927_: *mut LeanObject,
    mut v_h__1_928_: *mut LeanObject,
    mut v_h__2_929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_931_: u8 = 0;
    v_zero_930_ = lean_unsigned_to_nat(0);
    v_isZero_931_ = lean_nat_dec_eq(v_x_926_, v_zero_930_);
    if v_isZero_931_ == 1 {
        let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_929_);
        v___x_932_ = lean_apply_1(v_h__1_928_, lean_box(0));
        return v___x_932_;
    } else {
        let mut v_one_933_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_928_);
        v_one_933_ = lean_unsigned_to_nat(1);
        v_n_934_ = lean_nat_sub(v_x_926_, v_one_933_);
        v___x_935_ = lean_apply_2(v_h__2_929_, v_n_934_, lean_box(0));
        return v___x_935_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___boxed(
    mut v_n_936_: *mut LeanObject,
    mut v_motive_937_: *mut LeanObject,
    mut v_x_938_: *mut LeanObject,
    mut v_x_939_: *mut LeanObject,
    mut v_h__1_940_: *mut LeanObject,
    mut v_h__2_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_942_: *mut LeanObject = core::ptr::null_mut();
    v_res_942_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(
        v_n_936_,
        v_motive_937_,
        v_x_938_,
        v_x_939_,
        v_h__1_940_,
        v_h__2_941_,
    );
    lean_dec(v_x_938_);
    lean_dec(v_n_936_);
    return v_res_942_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(
    mut v_x_943_: *mut LeanObject,
    mut v_x_944_: *mut LeanObject,
    mut v_h__1_945_: *mut LeanObject,
    mut v_h__2_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_948_: u8 = 0;
    v_zero_947_ = lean_unsigned_to_nat(0);
    v_isZero_948_ = lean_nat_dec_eq(v_x_943_, v_zero_947_);
    if v_isZero_948_ == 1 {
        let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_946_);
        v___x_949_ = lean_apply_1(v_h__1_945_, v_x_944_);
        return v___x_949_;
    } else {
        let mut v_one_950_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_945_);
        v_one_950_ = lean_unsigned_to_nat(1);
        v_n_951_ = lean_nat_sub(v_x_943_, v_one_950_);
        v___x_952_ = lean_apply_2(v_h__2_946_, v_n_951_, v_x_944_);
        return v___x_952_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg___boxed(
    mut v_x_953_: *mut LeanObject,
    mut v_x_954_: *mut LeanObject,
    mut v_h__1_955_: *mut LeanObject,
    mut v_h__2_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_957_: *mut LeanObject = core::ptr::null_mut();
    v_res_957_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(
        v_x_953_,
        v_x_954_,
        v_h__1_955_,
        v_h__2_956_,
    );
    lean_dec(v_x_953_);
    return v_res_957_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(
    mut v_motive_958_: *mut LeanObject,
    mut v_x_959_: *mut LeanObject,
    mut v_x_960_: *mut LeanObject,
    mut v_h__1_961_: *mut LeanObject,
    mut v_h__2_962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_964_: u8 = 0;
    v_zero_963_ = lean_unsigned_to_nat(0);
    v_isZero_964_ = lean_nat_dec_eq(v_x_959_, v_zero_963_);
    if v_isZero_964_ == 1 {
        let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_962_);
        v___x_965_ = lean_apply_1(v_h__1_961_, v_x_960_);
        return v___x_965_;
    } else {
        let mut v_one_966_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_961_);
        v_one_966_ = lean_unsigned_to_nat(1);
        v_n_967_ = lean_nat_sub(v_x_959_, v_one_966_);
        v___x_968_ = lean_apply_2(v_h__2_962_, v_n_967_, v_x_960_);
        return v___x_968_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___boxed(
    mut v_motive_969_: *mut LeanObject,
    mut v_x_970_: *mut LeanObject,
    mut v_x_971_: *mut LeanObject,
    mut v_h__1_972_: *mut LeanObject,
    mut v_h__2_973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_974_: *mut LeanObject = core::ptr::null_mut();
    v_res_974_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(
        v_motive_969_,
        v_x_970_,
        v_x_971_,
        v_h__1_972_,
        v_h__2_973_,
    );
    lean_dec(v_x_970_);
    return v_res_974_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12()
-> *mut LeanObject {
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    v___x_1001_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10;
    v___x_1002_ = l_Lean_mkAtom(v___x_1001_);
    return v___x_1002_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13()
-> *mut LeanObject {
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_1003_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    v___x_1016_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16;
    v___x_1017_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5;
    v___x_1018_ = lean_array_push(v___x_1017_, v___x_1016_);
    return v___x_1018_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18()
-> *mut LeanObject {
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    v___x_1019_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17,
    );
    v___x_1020_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15;
    v___x_1021_ = lean_box(2);
    v___x_1022_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1022_, 0, v___x_1021_);
    lean_ctor_set(v___x_1022_, 1, v___x_1020_);
    lean_ctor_set(v___x_1022_, 2, v___x_1019_);
    return v___x_1022_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19()
-> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18,
    );
    v___x_1024_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    v___x_1026_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19,
    );
    v___x_1027_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11;
    v___x_1028_ = lean_box(2);
    v___x_1029_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1029_, 0, v___x_1028_);
    lean_ctor_set(v___x_1029_, 1, v___x_1027_);
    lean_ctor_set(v___x_1029_, 2, v___x_1026_);
    return v___x_1029_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21()
-> *mut LeanObject {
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1030_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    v___x_1033_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21,
    );
    v___x_1034_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9;
    v___x_1035_ = lean_box(2);
    v___x_1036_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1036_, 0, v___x_1035_);
    lean_ctor_set(v___x_1036_, 1, v___x_1034_);
    lean_ctor_set(v___x_1036_, 2, v___x_1033_);
    return v___x_1036_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23()
-> *mut LeanObject {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    v___x_1037_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1040_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23,
    );
    v___x_1041_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7;
    v___x_1042_ = lean_box(2);
    v___x_1043_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1043_, 0, v___x_1042_);
    lean_ctor_set(v___x_1043_, 1, v___x_1041_);
    lean_ctor_set(v___x_1043_, 2, v___x_1040_);
    return v___x_1043_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25()
-> *mut LeanObject {
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    v___x_1044_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    v___x_1047_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once
        ),
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25,
    );
    v___x_1048_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4;
    v___x_1049_ = lean_box(2);
    v___x_1050_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1050_, 0, v___x_1049_);
    lean_ctor_set(v___x_1050_, 1, v___x_1048_);
    lean_ctor_set(v___x_1050_, 2, v___x_1047_);
    return v___x_1050_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1() -> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ = lean_obj_once(
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
    mut v_x_1052_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1052_);
    return v_x_1052_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(
    mut v_x_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v_res_1054_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(v_x_1053_);
    lean_dec(v_x_1053_);
    return v_res_1054_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(
    mut v_n_1055_: *mut LeanObject,
    mut v_00_u03b1_1056_: *mut LeanObject,
    mut v_i_1057_: *mut LeanObject,
    mut v_j_1058_: *mut LeanObject,
    mut v_hi_1059_: *mut LeanObject,
    mut v_w_1060_: *mut LeanObject,
    mut v_x_1061_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1061_);
    return v_x_1061_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(
    mut v_n_1062_: *mut LeanObject,
    mut v_00_u03b1_1063_: *mut LeanObject,
    mut v_i_1064_: *mut LeanObject,
    mut v_j_1065_: *mut LeanObject,
    mut v_hi_1066_: *mut LeanObject,
    mut v_w_1067_: *mut LeanObject,
    mut v_x_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1069_: *mut LeanObject = core::ptr::null_mut();
    v_res_1069_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(
        v_n_1062_,
        v_00_u03b1_1063_,
        v_i_1064_,
        v_j_1065_,
        v_hi_1066_,
        v_w_1067_,
        v_x_1068_,
    );
    lean_dec(v_x_1068_);
    lean_dec(v_j_1065_);
    lean_dec(v_i_1064_);
    lean_dec(v_n_1062_);
    return v_res_1069_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9()
-> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1071_ = lean_obj_once(
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
pub unsafe fn _init_l_Nat_dfold___auto__1() -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_obj_once(
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
    mut v_n_1073_: *mut LeanObject,
    mut v_f_1074_: *mut LeanObject,
    mut v_j_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1078_: u8 = 0;
    let mut v_one_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1077_ = lean_unsigned_to_nat(0);
                v_isZero_1078_ = lean_nat_dec_eq(v_j_1075_, v_zero_1077_);
                if v_isZero_1078_ == 1 {
                    lean_dec(v_j_1075_);
                    lean_dec(v_f_1074_);
                    return v_a_1076_;
                } else {
                    v_one_1079_ = lean_unsigned_to_nat(1);
                    v_n_1080_ = lean_nat_sub(v_j_1075_, v_one_1079_);
                    v___x_1081_ = lean_nat_sub(v_n_1073_, v_j_1075_);
                    lean_dec(v_j_1075_);
                    lean_inc(v_f_1074_);
                    v___x_1082_ = lean_apply_3(v_f_1074_, v___x_1081_, lean_box(0), v_a_1076_);
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
    mut v_n_1084_: *mut LeanObject,
    mut v_f_1085_: *mut LeanObject,
    mut v_j_1086_: *mut LeanObject,
    mut v_a_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1088_: *mut LeanObject = core::ptr::null_mut();
    v_res_1088_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1084_, v_f_1085_, v_j_1086_, v_a_1087_,
    );
    lean_dec(v_n_1084_);
    return v_res_1088_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(
    mut v_n_1089_: *mut LeanObject,
    mut v_00_u03b1_1090_: *mut LeanObject,
    mut v_f_1091_: *mut LeanObject,
    mut v_j_1092_: *mut LeanObject,
    mut v_a_1093_: *mut LeanObject,
    mut v_a_1094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    v___x_1095_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1089_, v_f_1091_, v_j_1092_, v_a_1094_,
    );
    return v___x_1095_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(
    mut v_n_1096_: *mut LeanObject,
    mut v_00_u03b1_1097_: *mut LeanObject,
    mut v_f_1098_: *mut LeanObject,
    mut v_j_1099_: *mut LeanObject,
    mut v_a_1100_: *mut LeanObject,
    mut v_a_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1102_: *mut LeanObject = core::ptr::null_mut();
    v_res_1102_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(
        v_n_1096_,
        v_00_u03b1_1097_,
        v_f_1098_,
        v_j_1099_,
        v_a_1100_,
        v_a_1101_,
    );
    lean_dec(v_n_1096_);
    return v_res_1102_;
}
pub unsafe fn l_Nat_dfold___redArg(
    mut v_n_1103_: *mut LeanObject,
    mut v_f_1104_: *mut LeanObject,
    mut v_init_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_1103_);
    v___x_1106_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1103_,
        v_f_1104_,
        v_n_1103_,
        v_init_1105_,
    );
    lean_dec(v_n_1103_);
    return v___x_1106_;
}
pub unsafe fn l_Nat_dfold(
    mut v_n_1107_: *mut LeanObject,
    mut v_00_u03b1_1108_: *mut LeanObject,
    mut v_f_1109_: *mut LeanObject,
    mut v_init_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_1107_);
    v___x_1111_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(
        v_n_1107_,
        v_f_1109_,
        v_n_1107_,
        v_init_1110_,
    );
    lean_dec(v_n_1107_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Nat_dfoldRev___auto__1() -> *mut LeanObject {
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    v___x_1112_ = lean_obj_once(
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
    mut v_f_1113_: *mut LeanObject,
    mut v_i_1114_: *mut LeanObject,
    mut v_h_1115_: *mut LeanObject,
    mut v___y_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    v___x_1117_ = lean_apply_3(v_f_1113_, v_i_1114_, lean_box(0), v___y_1116_);
    return v___x_1117_;
}
pub unsafe fn l_Nat_dfoldRev___redArg(
    mut v_n_1118_: *mut LeanObject,
    mut v_f_1119_: *mut LeanObject,
    mut v_init_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1122_: u8 = 0;
    let mut v___f_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1121_ = lean_unsigned_to_nat(0);
                v_isZero_1122_ = lean_nat_dec_eq(v_n_1118_, v_zero_1121_);
                if v_isZero_1122_ == 1 {
                    lean_dec(v_f_1119_);
                    lean_dec(v_n_1118_);
                    return v_init_1120_;
                } else {
                    lean_inc(v_f_1119_);
                    v___f_1123_ = lean_alloc_closure(
                        l_Nat_dfoldRev___redArg___lam__0 as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    lean_closure_set(v___f_1123_, 0, v_f_1119_);
                    v_one_1124_ = lean_unsigned_to_nat(1);
                    v_n_1125_ = lean_nat_sub(v_n_1118_, v_one_1124_);
                    lean_dec(v_n_1118_);
                    lean_inc(v_n_1125_);
                    v___x_1126_ = lean_apply_3(v_f_1119_, v_n_1125_, lean_box(0), v_init_1120_);
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
    mut v_n_1128_: *mut LeanObject,
    mut v_00_u03b1_1129_: *mut LeanObject,
    mut v_f_1130_: *mut LeanObject,
    mut v_init_1131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = l_Nat_dfoldRev___redArg(v_n_1128_, v_f_1130_, v_init_1131_);
    return v___x_1132_;
}
pub unsafe fn _init_l_Nat_dfold__zero___auto__1() -> *mut LeanObject {
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    v___x_1133_ = lean_obj_once(
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
    mut v_x_1134_: *mut LeanObject,
    mut v_x_1135_: *mut LeanObject,
    mut v_h__1_1136_: *mut LeanObject,
    mut v_h__2_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1139_: u8 = 0;
    v_zero_1138_ = lean_unsigned_to_nat(0);
    v_isZero_1139_ = lean_nat_dec_eq(v_x_1134_, v_zero_1138_);
    if v_isZero_1139_ == 1 {
        let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1137_);
        v___x_1140_ = lean_apply_2(v_h__1_1136_, lean_box(0), v_x_1135_);
        return v___x_1140_;
    } else {
        let mut v_one_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1136_);
        v_one_1141_ = lean_unsigned_to_nat(1);
        v_n_1142_ = lean_nat_sub(v_x_1134_, v_one_1141_);
        v___x_1143_ = lean_apply_3(v_h__2_1137_, v_n_1142_, lean_box(0), v_x_1135_);
        return v___x_1143_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg___boxed(
    mut v_x_1144_: *mut LeanObject,
    mut v_x_1145_: *mut LeanObject,
    mut v_h__1_1146_: *mut LeanObject,
    mut v_h__2_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_res_1148_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(
        v_x_1144_,
        v_x_1145_,
        v_h__1_1146_,
        v_h__2_1147_,
    );
    lean_dec(v_x_1144_);
    return v_res_1148_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(
    mut v_n_1149_: *mut LeanObject,
    mut v_00_u03b1_1150_: *mut LeanObject,
    mut v_motive_1151_: *mut LeanObject,
    mut v_x_1152_: *mut LeanObject,
    mut v_x_1153_: *mut LeanObject,
    mut v_x_1154_: *mut LeanObject,
    mut v_h__1_1155_: *mut LeanObject,
    mut v_h__2_1156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1158_: u8 = 0;
    v_zero_1157_ = lean_unsigned_to_nat(0);
    v_isZero_1158_ = lean_nat_dec_eq(v_x_1152_, v_zero_1157_);
    if v_isZero_1158_ == 1 {
        let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1156_);
        v___x_1159_ = lean_apply_2(v_h__1_1155_, lean_box(0), v_x_1154_);
        return v___x_1159_;
    } else {
        let mut v_one_1160_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1155_);
        v_one_1160_ = lean_unsigned_to_nat(1);
        v_n_1161_ = lean_nat_sub(v_x_1152_, v_one_1160_);
        v___x_1162_ = lean_apply_3(v_h__2_1156_, v_n_1161_, lean_box(0), v_x_1154_);
        return v___x_1162_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___boxed(
    mut v_n_1163_: *mut LeanObject,
    mut v_00_u03b1_1164_: *mut LeanObject,
    mut v_motive_1165_: *mut LeanObject,
    mut v_x_1166_: *mut LeanObject,
    mut v_x_1167_: *mut LeanObject,
    mut v_x_1168_: *mut LeanObject,
    mut v_h__1_1169_: *mut LeanObject,
    mut v_h__2_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1171_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x_1166_);
    lean_dec(v_n_1163_);
    return v_res_1171_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5()
-> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ = lean_obj_once(
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
pub unsafe fn _init_l_Nat_dfold__succ___auto__3() -> *mut LeanObject {
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    v___x_1173_ = lean_obj_once(
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
pub unsafe fn _init_l_Nat_dfold__congr___auto__1() -> *mut LeanObject {
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    v___x_1174_ = lean_obj_once(
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
pub unsafe fn _init_l_Nat_dfold__add___auto__5() -> *mut LeanObject {
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___x_1175_ = lean_obj_once(
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
pub unsafe fn _init_l_Nat_dfoldRev__zero___auto__1() -> *mut LeanObject {
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    v___x_1176_ = lean_obj_once(
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
    mut v_n_1177_: *mut LeanObject,
    mut v_f_1178_: *mut LeanObject,
    mut v_init_1179_: *mut LeanObject,
    mut v_h__1_1180_: *mut LeanObject,
    mut v_h__2_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1183_: u8 = 0;
    v_zero_1182_ = lean_unsigned_to_nat(0);
    v_isZero_1183_ = lean_nat_dec_eq(v_n_1177_, v_zero_1182_);
    if v_isZero_1183_ == 1 {
        let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1181_);
        v___x_1184_ = lean_apply_3(v_h__1_1180_, lean_box(0), v_f_1178_, v_init_1179_);
        return v___x_1184_;
    } else {
        let mut v_one_1185_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1180_);
        v_one_1185_ = lean_unsigned_to_nat(1);
        v_n_1186_ = lean_nat_sub(v_n_1177_, v_one_1185_);
        v___x_1187_ = lean_apply_4(
            v_h__2_1181_,
            v_n_1186_,
            lean_box(0),
            v_f_1178_,
            v_init_1179_,
        );
        return v___x_1187_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg___boxed(
    mut v_n_1188_: *mut LeanObject,
    mut v_f_1189_: *mut LeanObject,
    mut v_init_1190_: *mut LeanObject,
    mut v_h__1_1191_: *mut LeanObject,
    mut v_h__2_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1193_: *mut LeanObject = core::ptr::null_mut();
    v_res_1193_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(
        v_n_1188_,
        v_f_1189_,
        v_init_1190_,
        v_h__1_1191_,
        v_h__2_1192_,
    );
    lean_dec(v_n_1188_);
    return v_res_1193_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(
    mut v_motive_1194_: *mut LeanObject,
    mut v_n_1195_: *mut LeanObject,
    mut v_00_u03b1_1196_: *mut LeanObject,
    mut v_f_1197_: *mut LeanObject,
    mut v_init_1198_: *mut LeanObject,
    mut v_h__1_1199_: *mut LeanObject,
    mut v_h__2_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1202_: u8 = 0;
    v_zero_1201_ = lean_unsigned_to_nat(0);
    v_isZero_1202_ = lean_nat_dec_eq(v_n_1195_, v_zero_1201_);
    if v_isZero_1202_ == 1 {
        let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1200_);
        v___x_1203_ = lean_apply_3(v_h__1_1199_, lean_box(0), v_f_1197_, v_init_1198_);
        return v___x_1203_;
    } else {
        let mut v_one_1204_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1199_);
        v_one_1204_ = lean_unsigned_to_nat(1);
        v_n_1205_ = lean_nat_sub(v_n_1195_, v_one_1204_);
        v___x_1206_ = lean_apply_4(
            v_h__2_1200_,
            v_n_1205_,
            lean_box(0),
            v_f_1197_,
            v_init_1198_,
        );
        return v___x_1206_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___boxed(
    mut v_motive_1207_: *mut LeanObject,
    mut v_n_1208_: *mut LeanObject,
    mut v_00_u03b1_1209_: *mut LeanObject,
    mut v_f_1210_: *mut LeanObject,
    mut v_init_1211_: *mut LeanObject,
    mut v_h__1_1212_: *mut LeanObject,
    mut v_h__2_1213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1214_: *mut LeanObject = core::ptr::null_mut();
    v_res_1214_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(
        v_motive_1207_,
        v_n_1208_,
        v_00_u03b1_1209_,
        v_f_1210_,
        v_init_1211_,
        v_h__1_1212_,
        v_h__2_1213_,
    );
    lean_dec(v_n_1208_);
    return v_res_1214_;
}
pub unsafe fn _init_l_Nat_dfoldRev__succ___auto__3() -> *mut LeanObject {
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    v___x_1215_ = lean_obj_once(
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
pub unsafe fn _init_l_Nat_dfoldRev__congr___auto__1() -> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v___x_1216_ = lean_obj_once(
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
pub unsafe fn _init_l_Nat_dfoldRev__add___auto__5() -> *mut LeanObject {
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1217_ = lean_obj_once(
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
    mut v_fst_1218_: *mut LeanObject,
    mut v_f_1219_: *mut LeanObject,
    mut v_j_1220_: *mut LeanObject,
    mut v_x_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v___x_1223_ = lean_nat_add(v_fst_1218_, v_j_1220_);
    v___x_1224_ = lean_apply_4(
        v_f_1219_,
        v___x_1223_,
        lean_box(0),
        lean_box(0),
        v___y_1222_,
    );
    return v___x_1224_;
}
pub unsafe fn l_Prod_foldI___redArg___lam__0___boxed(
    mut v_fst_1225_: *mut LeanObject,
    mut v_f_1226_: *mut LeanObject,
    mut v_j_1227_: *mut LeanObject,
    mut v_x_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1230_: *mut LeanObject = core::ptr::null_mut();
    v_res_1230_ =
        l_Prod_foldI___redArg___lam__0(v_fst_1225_, v_f_1226_, v_j_1227_, v_x_1228_, v___y_1229_);
    lean_dec(v_j_1227_);
    lean_dec(v_fst_1225_);
    return v_res_1230_;
}
pub unsafe fn l_Prod_foldI___redArg(
    mut v_i_1231_: *mut LeanObject,
    mut v_f_1232_: *mut LeanObject,
    mut v_init_1233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1234_ = lean_ctor_get(v_i_1231_, 0);
    lean_inc_n(v_fst_1234_, 2);
    v_snd_1235_ = lean_ctor_get(v_i_1231_, 1);
    lean_inc(v_snd_1235_);
    lean_dec_ref(v_i_1231_);
    v___f_1236_ = lean_alloc_closure(
        l_Prod_foldI___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1236_, 0, v_fst_1234_);
    lean_closure_set(v___f_1236_, 1, v_f_1232_);
    v___x_1237_ = lean_nat_sub(v_snd_1235_, v_fst_1234_);
    lean_dec(v_fst_1234_);
    lean_dec(v_snd_1235_);
    lean_inc(v___x_1237_);
    v___x_1238_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v___x_1237_,
        v___f_1236_,
        v___x_1237_,
        v_init_1233_,
    );
    lean_dec(v___x_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Prod_foldI(
    mut v_00_u03b1_1239_: *mut LeanObject,
    mut v_i_1240_: *mut LeanObject,
    mut v_f_1241_: *mut LeanObject,
    mut v_init_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1243_ = lean_ctor_get(v_i_1240_, 0);
    lean_inc_n(v_fst_1243_, 2);
    v_snd_1244_ = lean_ctor_get(v_i_1240_, 1);
    lean_inc(v_snd_1244_);
    lean_dec_ref(v_i_1240_);
    v___f_1245_ = lean_alloc_closure(
        l_Prod_foldI___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1245_, 0, v_fst_1243_);
    lean_closure_set(v___f_1245_, 1, v_f_1241_);
    v___x_1246_ = lean_nat_sub(v_snd_1244_, v_fst_1243_);
    lean_dec(v_fst_1243_);
    lean_dec(v_snd_1244_);
    lean_inc(v___x_1246_);
    v___x_1247_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(
        v___x_1246_,
        v___f_1245_,
        v___x_1246_,
        v_init_1242_,
    );
    lean_dec(v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Prod_anyI___lam__0(
    mut v_fst_1248_: *mut LeanObject,
    mut v_f_1249_: *mut LeanObject,
    mut v_j_1250_: *mut LeanObject,
    mut v_x_1251_: *mut LeanObject,
) -> u8 {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    v___x_1252_ = lean_nat_add(v_fst_1248_, v_j_1250_);
    v___x_1253_ = lean_apply_3(v_f_1249_, v___x_1252_, lean_box(0), lean_box(0));
    v___x_1254_ = (lean_unbox(v___x_1253_) as u8);
    return v___x_1254_;
}
pub unsafe fn l_Prod_anyI___lam__0___boxed(
    mut v_fst_1255_: *mut LeanObject,
    mut v_f_1256_: *mut LeanObject,
    mut v_j_1257_: *mut LeanObject,
    mut v_x_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1259_: u8 = 0;
    let mut v_r_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Prod_anyI___lam__0(v_fst_1255_, v_f_1256_, v_j_1257_, v_x_1258_);
    lean_dec(v_j_1257_);
    lean_dec(v_fst_1255_);
    v_r_1260_ = lean_box((v_res_1259_) as usize);
    return v_r_1260_;
}
pub unsafe fn l_Prod_anyI(mut v_i_1261_: *mut LeanObject, mut v_f_1262_: *mut LeanObject) -> u8 {
    let mut v_fst_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    v_fst_1263_ = lean_ctor_get(v_i_1261_, 0);
    lean_inc_n(v_fst_1263_, 2);
    v_snd_1264_ = lean_ctor_get(v_i_1261_, 1);
    lean_inc(v_snd_1264_);
    lean_dec_ref(v_i_1261_);
    v___f_1265_ = lean_alloc_closure(l_Prod_anyI___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_1265_, 0, v_fst_1263_);
    lean_closure_set(v___f_1265_, 1, v_f_1262_);
    v___x_1266_ = lean_nat_sub(v_snd_1264_, v_fst_1263_);
    lean_dec(v_fst_1263_);
    lean_dec(v_snd_1264_);
    lean_inc(v___x_1266_);
    v___x_1267_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(
        v___x_1266_,
        v___f_1265_,
        v___x_1266_,
    );
    lean_dec(v___x_1266_);
    return v___x_1267_;
}
pub unsafe fn l_Prod_anyI___boxed(
    mut v_i_1268_: *mut LeanObject,
    mut v_f_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1270_: u8 = 0;
    let mut v_r_1271_: *mut LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Prod_anyI(v_i_1268_, v_f_1269_);
    v_r_1271_ = lean_box((v_res_1270_) as usize);
    return v_r_1271_;
}
pub unsafe fn l_Prod_allI(mut v_i_1272_: *mut LeanObject, mut v_f_1273_: *mut LeanObject) -> u8 {
    let mut v_fst_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    v_fst_1274_ = lean_ctor_get(v_i_1272_, 0);
    lean_inc_n(v_fst_1274_, 2);
    v_snd_1275_ = lean_ctor_get(v_i_1272_, 1);
    lean_inc(v_snd_1275_);
    lean_dec_ref(v_i_1272_);
    v___f_1276_ = lean_alloc_closure(l_Prod_anyI___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_1276_, 0, v_fst_1274_);
    lean_closure_set(v___f_1276_, 1, v_f_1273_);
    v___x_1277_ = lean_nat_sub(v_snd_1275_, v_fst_1274_);
    lean_dec(v_fst_1274_);
    lean_dec(v_snd_1275_);
    lean_inc(v___x_1277_);
    v___x_1278_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(
        v___x_1277_,
        v___f_1276_,
        v___x_1277_,
    );
    lean_dec(v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Prod_allI___boxed(
    mut v_i_1279_: *mut LeanObject,
    mut v_f_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1281_: u8 = 0;
    let mut v_r_1282_: *mut LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Prod_allI(v_i_1279_, v_f_1280_);
    v_r_1282_ = lean_box((v_res_1281_) as usize);
    return v_r_1282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Fold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_FinRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Fold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1();
    lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1);
    l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9();
    lean_mark_persistent(
        l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9,
    );
    l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3();
    lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3);
    l_Nat_dfold___auto__1 = _init_l_Nat_dfold___auto__1();
    lean_mark_persistent(l_Nat_dfold___auto__1);
    l_Nat_dfoldRev___auto__1 = _init_l_Nat_dfoldRev___auto__1();
    lean_mark_persistent(l_Nat_dfoldRev___auto__1);
    l_Nat_dfold__zero___auto__1 = _init_l_Nat_dfold__zero___auto__1();
    lean_mark_persistent(l_Nat_dfold__zero___auto__1);
    l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5 =
        _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5();
    lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5);
    l_Nat_dfold__succ___auto__3 = _init_l_Nat_dfold__succ___auto__3();
    lean_mark_persistent(l_Nat_dfold__succ___auto__3);
    l_Nat_dfold__congr___auto__1 = _init_l_Nat_dfold__congr___auto__1();
    lean_mark_persistent(l_Nat_dfold__congr___auto__1);
    l_Nat_dfold__add___auto__5 = _init_l_Nat_dfold__add___auto__5();
    lean_mark_persistent(l_Nat_dfold__add___auto__5);
    l_Nat_dfoldRev__zero___auto__1 = _init_l_Nat_dfoldRev__zero___auto__1();
    lean_mark_persistent(l_Nat_dfoldRev__zero___auto__1);
    l_Nat_dfoldRev__succ___auto__3 = _init_l_Nat_dfoldRev__succ___auto__3();
    lean_mark_persistent(l_Nat_dfoldRev__succ___auto__3);
    l_Nat_dfoldRev__congr___auto__1 = _init_l_Nat_dfoldRev__congr___auto__1();
    lean_mark_persistent(l_Nat_dfoldRev__congr___auto__1);
    l_Nat_dfoldRev__add___auto__5 = _init_l_Nat_dfoldRev__add___auto__5();
    lean_mark_persistent(l_Nat_dfoldRev__add___auto__5);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Fold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_FinRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Nat_Fold(builtin);
}
