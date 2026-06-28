// Lean compiler output
// Module: Init.Data.List.Sort.Basic
// Imports: Init.Ext Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Data.Nat.Lemmas Init.Omega
use crate::r#gen::Init::Data::List::Basic::l_List_splitAt___redArg;
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom, l_List_lengthTR___redArg,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le,
    lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_box, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_List_merge___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_List_merge___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_List_merge___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_List_merge___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_List_merge___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__3_value) as *mut LeanObject;
static l_List_merge___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_List_merge___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_List_merge___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__5_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
static mut l_List_merge___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__6_value) as *mut LeanObject;
static l_List_merge___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_List_merge___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_List_merge___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__8_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__9_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__10_value) as *mut LeanObject;
static l_List_merge___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_List_merge___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__10_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__14_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__14_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__15_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__15_value) as *mut LeanObject;
static l_List_merge___auto__1___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__14_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_List_merge___auto__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__15_value) as *mut LeanObject,
        7043493786777132025 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__19_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__19_value) as *mut LeanObject;
static l_List_merge___auto__1___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_List_merge___auto__1___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__14_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_List_merge___auto__1___closed__20_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__19_value) as *mut LeanObject,
        16077784126176397009 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__21_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__21_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__24_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__21_value) as *mut LeanObject,
        7839396180116328695 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__24_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__27_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__27_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__29: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__30_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__27_value) as *mut LeanObject,
        10300200614825825839 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__30_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__31: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__32: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__33_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__33: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__35_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_merge___auto__1___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__35_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__36_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__36: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__37_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__37_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__38_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__38: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__39_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__39: *mut LeanObject = core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__40_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__40_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__41_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_merge___auto__1___closed__40_value) as *mut LeanObject,
        8748957123817046895 as *mut LeanObject,
    ],
};
static mut l_List_merge___auto__1___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__41_value) as *mut LeanObject;
pub static l_List_merge___auto__1___closed__42_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_merge___auto__1___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__42_value) as *mut LeanObject;
static mut l_List_merge___auto__1___closed__43_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__43: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__44_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__44: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__45_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__45: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__46_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__46: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__47_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__47: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__48_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__48: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__49_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__49: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__50_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__50: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__51_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__51: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__52_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__52: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__53_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__53: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__54_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__54: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__55_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__55: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__56_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__56: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__57_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__57: *mut LeanObject = core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__58_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_merge___auto__1___closed__58: *mut LeanObject = core::ptr::null_mut();
pub static mut l_List_merge___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_List_mergeSort___auto__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_List_merge___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ = l_List_merge___auto__1___closed__10;
    v___x_349_ = l_Lean_mkAtom(v___x_348_);
    return v___x_349_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__12_once),
        _init_l_List_merge___auto__1___closed__12,
    );
    v___x_351_ = l_List_merge___auto__1___closed__5;
    v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    v___x_360_ = l_List_merge___auto__1___closed__15;
    v___x_361_ = l_Lean_mkAtom(v___x_360_);
    return v___x_361_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__17_once),
        _init_l_List_merge___auto__1___closed__17,
    );
    v___x_363_ = l_List_merge___auto__1___closed__5;
    v___x_364_ = lean_array_push(v___x_363_, v___x_362_);
    return v___x_364_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v___x_372_ = l_List_merge___auto__1___closed__21;
    v___x_373_ = lean_string_utf8_byte_size(v___x_372_);
    return v___x_373_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    v___x_374_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__22_once),
        _init_l_List_merge___auto__1___closed__22,
    );
    v___x_375_ = lean_unsigned_to_nat(0);
    v___x_376_ = l_List_merge___auto__1___closed__21;
    v___x_377_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_377_, 0, v___x_376_);
    lean_ctor_set(v___x_377_, 1, v___x_375_);
    lean_ctor_set(v___x_377_, 2, v___x_374_);
    return v___x_377_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = lean_box(0);
    v___x_381_ = l_List_merge___auto__1___closed__24;
    v___x_382_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__23_once),
        _init_l_List_merge___auto__1___closed__23,
    );
    v___x_383_ = lean_box(2);
    v___x_384_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_384_, 0, v___x_383_);
    lean_ctor_set(v___x_384_, 1, v___x_382_);
    lean_ctor_set(v___x_384_, 2, v___x_381_);
    lean_ctor_set(v___x_384_, 3, v___x_380_);
    return v___x_384_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___x_385_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__25_once),
        _init_l_List_merge___auto__1___closed__25,
    );
    v___x_386_ = l_List_merge___auto__1___closed__5;
    v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
    return v___x_387_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_389_ = l_List_merge___auto__1___closed__27;
    v___x_390_ = lean_string_utf8_byte_size(v___x_389_);
    return v___x_390_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__29() -> *mut LeanObject {
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__28_once),
        _init_l_List_merge___auto__1___closed__28,
    );
    v___x_392_ = lean_unsigned_to_nat(0);
    v___x_393_ = l_List_merge___auto__1___closed__27;
    v___x_394_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_394_, 0, v___x_393_);
    lean_ctor_set(v___x_394_, 1, v___x_392_);
    lean_ctor_set(v___x_394_, 2, v___x_391_);
    return v___x_394_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__31() -> *mut LeanObject {
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_397_ = lean_box(0);
    v___x_398_ = l_List_merge___auto__1___closed__30;
    v___x_399_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__29_once),
        _init_l_List_merge___auto__1___closed__29,
    );
    v___x_400_ = lean_box(2);
    v___x_401_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_401_, 0, v___x_400_);
    lean_ctor_set(v___x_401_, 1, v___x_399_);
    lean_ctor_set(v___x_401_, 2, v___x_398_);
    lean_ctor_set(v___x_401_, 3, v___x_397_);
    return v___x_401_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__32() -> *mut LeanObject {
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    v___x_402_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31_once),
        _init_l_List_merge___auto__1___closed__31,
    );
    v___x_403_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26_once),
        _init_l_List_merge___auto__1___closed__26,
    );
    v___x_404_ = lean_array_push(v___x_403_, v___x_402_);
    return v___x_404_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__33() -> *mut LeanObject {
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    v___x_405_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__32_once),
        _init_l_List_merge___auto__1___closed__32,
    );
    v___x_406_ = l_List_merge___auto__1___closed__9;
    v___x_407_ = lean_box(2);
    v___x_408_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_408_, 0, v___x_407_);
    lean_ctor_set(v___x_408_, 1, v___x_406_);
    lean_ctor_set(v___x_408_, 2, v___x_405_);
    return v___x_408_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__34() -> *mut LeanObject {
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    v___x_409_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__33_once),
        _init_l_List_merge___auto__1___closed__33,
    );
    v___x_410_ = l_List_merge___auto__1___closed__5;
    v___x_411_ = lean_array_push(v___x_410_, v___x_409_);
    return v___x_411_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__36() -> *mut LeanObject {
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    v___x_416_ = l_List_merge___auto__1___closed__35;
    v___x_417_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__34_once),
        _init_l_List_merge___auto__1___closed__34,
    );
    v___x_418_ = lean_array_push(v___x_417_, v___x_416_);
    return v___x_418_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__38() -> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    v___x_420_ = l_List_merge___auto__1___closed__37;
    v___x_421_ = l_Lean_mkAtom(v___x_420_);
    return v___x_421_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__39() -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__38_once),
        _init_l_List_merge___auto__1___closed__38,
    );
    v___x_423_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__36_once),
        _init_l_List_merge___auto__1___closed__36,
    );
    v___x_424_ = lean_array_push(v___x_423_, v___x_422_);
    return v___x_424_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__43() -> *mut LeanObject {
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_429_ = l_List_merge___auto__1___closed__42;
    v___x_430_ = l_Lean_mkAtom(v___x_429_);
    return v___x_430_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__44() -> *mut LeanObject {
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    v___x_431_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__43_once),
        _init_l_List_merge___auto__1___closed__43,
    );
    v___x_432_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26_once),
        _init_l_List_merge___auto__1___closed__26,
    );
    v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
    return v___x_433_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__45() -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v___x_434_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31_once),
        _init_l_List_merge___auto__1___closed__31,
    );
    v___x_435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__44_once),
        _init_l_List_merge___auto__1___closed__44,
    );
    v___x_436_ = lean_array_push(v___x_435_, v___x_434_);
    return v___x_436_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__46() -> *mut LeanObject {
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__45_once),
        _init_l_List_merge___auto__1___closed__45,
    );
    v___x_438_ = l_List_merge___auto__1___closed__41;
    v___x_439_ = lean_box(2);
    v___x_440_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_440_, 0, v___x_439_);
    lean_ctor_set(v___x_440_, 1, v___x_438_);
    lean_ctor_set(v___x_440_, 2, v___x_437_);
    return v___x_440_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__47() -> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_441_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__46_once),
        _init_l_List_merge___auto__1___closed__46,
    );
    v___x_442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__39_once),
        _init_l_List_merge___auto__1___closed__39,
    );
    v___x_443_ = lean_array_push(v___x_442_, v___x_441_);
    return v___x_443_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__48() -> *mut LeanObject {
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    v___x_444_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__47_once),
        _init_l_List_merge___auto__1___closed__47,
    );
    v___x_445_ = l_List_merge___auto__1___closed__20;
    v___x_446_ = lean_box(2);
    v___x_447_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_447_, 0, v___x_446_);
    lean_ctor_set(v___x_447_, 1, v___x_445_);
    lean_ctor_set(v___x_447_, 2, v___x_444_);
    return v___x_447_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__49() -> *mut LeanObject {
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    v___x_448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__48_once),
        _init_l_List_merge___auto__1___closed__48,
    );
    v___x_449_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__18_once),
        _init_l_List_merge___auto__1___closed__18,
    );
    v___x_450_ = lean_array_push(v___x_449_, v___x_448_);
    return v___x_450_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__50() -> *mut LeanObject {
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    v___x_451_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__49),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__49_once),
        _init_l_List_merge___auto__1___closed__49,
    );
    v___x_452_ = l_List_merge___auto__1___closed__16;
    v___x_453_ = lean_box(2);
    v___x_454_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_454_, 0, v___x_453_);
    lean_ctor_set(v___x_454_, 1, v___x_452_);
    lean_ctor_set(v___x_454_, 2, v___x_451_);
    return v___x_454_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__51() -> *mut LeanObject {
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    v___x_455_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__50_once),
        _init_l_List_merge___auto__1___closed__50,
    );
    v___x_456_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__13_once),
        _init_l_List_merge___auto__1___closed__13,
    );
    v___x_457_ = lean_array_push(v___x_456_, v___x_455_);
    return v___x_457_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__52() -> *mut LeanObject {
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v___x_458_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__51_once),
        _init_l_List_merge___auto__1___closed__51,
    );
    v___x_459_ = l_List_merge___auto__1___closed__11;
    v___x_460_ = lean_box(2);
    v___x_461_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_461_, 0, v___x_460_);
    lean_ctor_set(v___x_461_, 1, v___x_459_);
    lean_ctor_set(v___x_461_, 2, v___x_458_);
    return v___x_461_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__53() -> *mut LeanObject {
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    v___x_462_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__52_once),
        _init_l_List_merge___auto__1___closed__52,
    );
    v___x_463_ = l_List_merge___auto__1___closed__5;
    v___x_464_ = lean_array_push(v___x_463_, v___x_462_);
    return v___x_464_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__54() -> *mut LeanObject {
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    v___x_465_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__53_once),
        _init_l_List_merge___auto__1___closed__53,
    );
    v___x_466_ = l_List_merge___auto__1___closed__9;
    v___x_467_ = lean_box(2);
    v___x_468_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_468_, 0, v___x_467_);
    lean_ctor_set(v___x_468_, 1, v___x_466_);
    lean_ctor_set(v___x_468_, 2, v___x_465_);
    return v___x_468_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__55() -> *mut LeanObject {
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___x_469_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__54_once),
        _init_l_List_merge___auto__1___closed__54,
    );
    v___x_470_ = l_List_merge___auto__1___closed__5;
    v___x_471_ = lean_array_push(v___x_470_, v___x_469_);
    return v___x_471_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__56() -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__55_once),
        _init_l_List_merge___auto__1___closed__55,
    );
    v___x_473_ = l_List_merge___auto__1___closed__7;
    v___x_474_ = lean_box(2);
    v___x_475_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_475_, 0, v___x_474_);
    lean_ctor_set(v___x_475_, 1, v___x_473_);
    lean_ctor_set(v___x_475_, 2, v___x_472_);
    return v___x_475_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__57() -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__56_once),
        _init_l_List_merge___auto__1___closed__56,
    );
    v___x_477_ = l_List_merge___auto__1___closed__5;
    v___x_478_ = lean_array_push(v___x_477_, v___x_476_);
    return v___x_478_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__58() -> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__57_once),
        _init_l_List_merge___auto__1___closed__57,
    );
    v___x_480_ = l_List_merge___auto__1___closed__4;
    v___x_481_ = lean_box(2);
    v___x_482_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_482_, 0, v___x_481_);
    lean_ctor_set(v___x_482_, 1, v___x_480_);
    lean_ctor_set(v___x_482_, 2, v___x_479_);
    return v___x_482_;
}
pub unsafe fn _init_l_List_merge___auto__1() -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58_once),
        _init_l_List_merge___auto__1___closed__58,
    );
    return v___x_483_;
}
pub unsafe fn l_List_merge___redArg(
    mut v_xs_484_: *mut LeanObject,
    mut v_ys_485_: *mut LeanObject,
    mut v_le_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: u8 = 0;
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_495_: u8 = 0;
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_500_: u8 = 0;
    let mut v_unused_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut v_unused_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_512_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_xs_484_) == 0 {
                    lean_dec_ref(v_le_486_);
                    return v_ys_485_;
                } else {
                    if lean_obj_tag(v_ys_485_) == 0 {
                        lean_dec_ref(v_le_486_);
                        return v_xs_484_;
                    } else {
                        v_head_487_ = lean_ctor_get(v_xs_484_, 0);
                        v_tail_488_ = lean_ctor_get(v_xs_484_, 1);
                        v_head_489_ = lean_ctor_get(v_ys_485_, 0);
                        v_tail_490_ = lean_ctor_get(v_ys_485_, 1);
                        lean_inc_ref(v_le_486_);
                        lean_inc(v_head_489_);
                        lean_inc(v_head_487_);
                        v___x_491_ = lean_apply_2(v_le_486_, v_head_487_, v_head_489_);
                        v___x_492_ = (lean_unbox(v___x_491_) as u8);
                        if v___x_492_ == 0 {
                            lean_inc(v_tail_490_);
                            lean_inc(v_head_489_);
                            v_isSharedCheck_500_ = (!lean_is_exclusive(v_ys_485_)) as u8;
                            if v_isSharedCheck_500_ == 0 {
                                v_unused_501_ = lean_ctor_get(v_ys_485_, 1);
                                lean_dec(v_unused_501_);
                                v_unused_502_ = lean_ctor_get(v_ys_485_, 0);
                                lean_dec(v_unused_502_);
                                v___x_494_ = v_ys_485_;
                                v_isShared_495_ = v_isSharedCheck_500_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_ys_485_);
                                v___x_494_ = lean_box(0);
                                v_isShared_495_ = v_isSharedCheck_500_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_inc(v_tail_488_);
                            lean_inc(v_head_487_);
                            v_isSharedCheck_510_ = (!lean_is_exclusive(v_xs_484_)) as u8;
                            if v_isSharedCheck_510_ == 0 {
                                v_unused_511_ = lean_ctor_get(v_xs_484_, 1);
                                lean_dec(v_unused_511_);
                                v_unused_512_ = lean_ctor_get(v_xs_484_, 0);
                                lean_dec(v_unused_512_);
                                v___x_504_ = v_xs_484_;
                                v_isShared_505_ = v_isSharedCheck_510_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_xs_484_);
                                v___x_504_ = lean_box(0);
                                v_isShared_505_ = v_isSharedCheck_510_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_496_ = l_List_merge___redArg(v_xs_484_, v_tail_490_, v_le_486_);
                if v_isShared_495_ == 0 {
                    lean_ctor_set(v___x_494_, 1, v___x_496_);
                    v___x_498_ = v___x_494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_499_, 0, v_head_489_);
                    lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
                    v___x_498_ = v_reuseFailAlloc_499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_498_;
            }
            3 => {
                v___x_506_ = l_List_merge___redArg(v_tail_488_, v_ys_485_, v_le_486_);
                if v_isShared_505_ == 0 {
                    lean_ctor_set(v___x_504_, 1, v___x_506_);
                    v___x_508_ = v___x_504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_509_, 0, v_head_487_);
                    lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_506_);
                    v___x_508_ = v_reuseFailAlloc_509_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_merge(
    mut v_00_u03b1_513_: *mut LeanObject,
    mut v_xs_514_: *mut LeanObject,
    mut v_ys_515_: *mut LeanObject,
    mut v_le_516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    v___x_517_ = l_List_merge___redArg(v_xs_514_, v_ys_515_, v_le_516_);
    return v___x_517_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter___redArg(
    mut v_xs_518_: *mut LeanObject,
    mut v_ys_519_: *mut LeanObject,
    mut v_h__1_520_: *mut LeanObject,
    mut v_h__2_521_: *mut LeanObject,
    mut v_h__3_522_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_518_) == 0 {
        let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_522_);
        lean_dec(v_h__2_521_);
        v___x_523_ = lean_apply_1(v_h__1_520_, v_ys_519_);
        return v___x_523_;
    } else {
        lean_dec(v_h__1_520_);
        if lean_obj_tag(v_ys_519_) == 0 {
            let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_522_);
            v___x_524_ = lean_apply_2(v_h__2_521_, v_xs_518_, lean_box(0));
            return v___x_524_;
        } else {
            let mut v_head_525_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_526_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_527_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_528_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_521_);
            v_head_525_ = lean_ctor_get(v_xs_518_, 0);
            lean_inc(v_head_525_);
            v_tail_526_ = lean_ctor_get(v_xs_518_, 1);
            lean_inc(v_tail_526_);
            lean_dec_ref_known(v_xs_518_, 2);
            v_head_527_ = lean_ctor_get(v_ys_519_, 0);
            lean_inc(v_head_527_);
            v_tail_528_ = lean_ctor_get(v_ys_519_, 1);
            lean_inc(v_tail_528_);
            lean_dec_ref_known(v_ys_519_, 2);
            v___x_529_ = lean_apply_4(
                v_h__3_522_,
                v_head_525_,
                v_tail_526_,
                v_head_527_,
                v_tail_528_,
            );
            return v___x_529_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter(
    mut v_00_u03b1_530_: *mut LeanObject,
    mut v_motive_531_: *mut LeanObject,
    mut v_xs_532_: *mut LeanObject,
    mut v_ys_533_: *mut LeanObject,
    mut v_h__1_534_: *mut LeanObject,
    mut v_h__2_535_: *mut LeanObject,
    mut v_h__3_536_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_532_) == 0 {
        let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_536_);
        lean_dec(v_h__2_535_);
        v___x_537_ = lean_apply_1(v_h__1_534_, v_ys_533_);
        return v___x_537_;
    } else {
        lean_dec(v_h__1_534_);
        if lean_obj_tag(v_ys_533_) == 0 {
            let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_536_);
            v___x_538_ = lean_apply_2(v_h__2_535_, v_xs_532_, lean_box(0));
            return v___x_538_;
        } else {
            let mut v_head_539_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_540_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_541_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_542_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_535_);
            v_head_539_ = lean_ctor_get(v_xs_532_, 0);
            lean_inc(v_head_539_);
            v_tail_540_ = lean_ctor_get(v_xs_532_, 1);
            lean_inc(v_tail_540_);
            lean_dec_ref_known(v_xs_532_, 2);
            v_head_541_ = lean_ctor_get(v_ys_533_, 0);
            lean_inc(v_head_541_);
            v_tail_542_ = lean_ctor_get(v_ys_533_, 1);
            lean_inc(v_tail_542_);
            lean_dec_ref_known(v_ys_533_, 2);
            v___x_543_ = lean_apply_4(
                v_h__3_536_,
                v_head_539_,
                v_tail_540_,
                v_head_541_,
                v_tail_542_,
            );
            return v___x_543_;
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_splitInTwo___redArg(
    mut v_n_544_: *mut LeanObject,
    mut v_l_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_554_: u8 = 0;
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_546_ = lean_unsigned_to_nat(1);
                v___x_547_ = lean_nat_add(v_n_544_, v___x_546_);
                v___x_548_ = lean_nat_shiftr(v___x_547_, v___x_546_);
                lean_dec(v___x_547_);
                v_r_549_ = l_List_splitAt___redArg(v___x_548_, v_l_545_);
                v_fst_550_ = lean_ctor_get(v_r_549_, 0);
                v_snd_551_ = lean_ctor_get(v_r_549_, 1);
                v_isSharedCheck_558_ = (!lean_is_exclusive(v_r_549_)) as u8;
                if v_isSharedCheck_558_ == 0 {
                    v___x_553_ = v_r_549_;
                    v_isShared_554_ = v_isSharedCheck_558_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_551_);
                    lean_inc(v_fst_550_);
                    lean_dec(v_r_549_);
                    v___x_553_ = lean_box(0);
                    v_isShared_554_ = v_isSharedCheck_558_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_554_ == 0 {
                    v___x_556_ = v___x_553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_557_, 0, v_fst_550_);
                    lean_ctor_set(v_reuseFailAlloc_557_, 1, v_snd_551_);
                    v___x_556_ = v_reuseFailAlloc_557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_splitInTwo___redArg___boxed(
    mut v_n_559_: *mut LeanObject,
    mut v_l_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_561_: *mut LeanObject = core::ptr::null_mut();
    v_res_561_ = l_List_MergeSort_Internal_splitInTwo___redArg(v_n_559_, v_l_560_);
    lean_dec(v_n_559_);
    return v_res_561_;
}
pub unsafe fn l_List_MergeSort_Internal_splitInTwo(
    mut v_00_u03b1_562_: *mut LeanObject,
    mut v_n_563_: *mut LeanObject,
    mut v_l_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    v___x_565_ = l_List_MergeSort_Internal_splitInTwo___redArg(v_n_563_, v_l_564_);
    return v___x_565_;
}
pub unsafe fn l_List_MergeSort_Internal_splitInTwo___boxed(
    mut v_00_u03b1_566_: *mut LeanObject,
    mut v_n_567_: *mut LeanObject,
    mut v_l_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_569_: *mut LeanObject = core::ptr::null_mut();
    v_res_569_ = l_List_MergeSort_Internal_splitInTwo(v_00_u03b1_566_, v_n_567_, v_l_568_);
    lean_dec(v_n_567_);
    return v_res_569_;
}
pub unsafe fn _init_l_List_mergeSort___auto__1() -> *mut LeanObject {
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    v___x_570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58_once),
        _init_l_List_merge___auto__1___closed__58,
    );
    return v___x_570_;
}
pub unsafe fn l_List_mergeSort___redArg(
    mut v_x_571_: *mut LeanObject,
    mut v_x_572_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_571_) == 0 {
        lean_dec_ref(v_x_572_);
        return v_x_571_;
    } else {
        let mut v_tail_573_: *mut LeanObject = core::ptr::null_mut();
        v_tail_573_ = lean_ctor_get(v_x_571_, 1);
        if lean_obj_tag(v_tail_573_) == 0 {
            lean_dec_ref(v_x_572_);
            return v_x_571_;
        } else {
            let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lr_575_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_576_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_577_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
            v___x_574_ = l_List_lengthTR___redArg(v_x_571_);
            v_lr_575_ = l_List_MergeSort_Internal_splitInTwo___redArg(v___x_574_, v_x_571_);
            lean_dec(v___x_574_);
            v_fst_576_ = lean_ctor_get(v_lr_575_, 0);
            lean_inc(v_fst_576_);
            v_snd_577_ = lean_ctor_get(v_lr_575_, 1);
            lean_inc(v_snd_577_);
            lean_dec_ref(v_lr_575_);
            lean_inc_ref_n(v_x_572_, 2);
            v___x_578_ = l_List_mergeSort___redArg(v_fst_576_, v_x_572_);
            v___x_579_ = l_List_mergeSort___redArg(v_snd_577_, v_x_572_);
            v___x_580_ = l_List_merge___redArg(v___x_578_, v___x_579_, v_x_572_);
            return v___x_580_;
        }
    }
}
pub unsafe fn l_List_mergeSort(
    mut v_00_u03b1_581_: *mut LeanObject,
    mut v_x_582_: *mut LeanObject,
    mut v_x_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    v___x_584_ = l_List_mergeSort___redArg(v_x_582_, v_x_583_);
    return v___x_584_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_585_: *mut LeanObject,
    mut v_x_586_: *mut LeanObject,
    mut v_h__1_587_: *mut LeanObject,
    mut v_h__2_588_: *mut LeanObject,
    mut v_h__3_589_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_585_) == 0 {
        let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_589_);
        lean_dec(v_h__2_588_);
        v___x_590_ = lean_apply_1(v_h__1_587_, v_x_586_);
        return v___x_590_;
    } else {
        let mut v_tail_591_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_587_);
        v_tail_591_ = lean_ctor_get(v_x_585_, 1);
        if lean_obj_tag(v_tail_591_) == 0 {
            let mut v_head_592_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_589_);
            v_head_592_ = lean_ctor_get(v_x_585_, 0);
            lean_inc(v_head_592_);
            lean_dec_ref_known(v_x_585_, 2);
            v___x_593_ = lean_apply_2(v_h__2_588_, v_head_592_, v_x_586_);
            return v___x_593_;
        } else {
            let mut v_head_594_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_595_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_596_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_591_);
            lean_dec(v_h__2_588_);
            v_head_594_ = lean_ctor_get(v_x_585_, 0);
            lean_inc(v_head_594_);
            lean_dec_ref_known(v_x_585_, 2);
            v_head_595_ = lean_ctor_get(v_tail_591_, 0);
            lean_inc(v_head_595_);
            v_tail_596_ = lean_ctor_get(v_tail_591_, 1);
            lean_inc(v_tail_596_);
            lean_dec_ref_known(v_tail_591_, 2);
            v___x_597_ = lean_apply_4(v_h__3_589_, v_head_594_, v_head_595_, v_tail_596_, v_x_586_);
            return v___x_597_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_598_: *mut LeanObject,
    mut v_motive_599_: *mut LeanObject,
    mut v_x_600_: *mut LeanObject,
    mut v_x_601_: *mut LeanObject,
    mut v_h__1_602_: *mut LeanObject,
    mut v_h__2_603_: *mut LeanObject,
    mut v_h__3_604_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_600_) == 0 {
        let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_604_);
        lean_dec(v_h__2_603_);
        v___x_605_ = lean_apply_1(v_h__1_602_, v_x_601_);
        return v___x_605_;
    } else {
        let mut v_tail_606_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_602_);
        v_tail_606_ = lean_ctor_get(v_x_600_, 1);
        if lean_obj_tag(v_tail_606_) == 0 {
            let mut v_head_607_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_604_);
            v_head_607_ = lean_ctor_get(v_x_600_, 0);
            lean_inc(v_head_607_);
            lean_dec_ref_known(v_x_600_, 2);
            v___x_608_ = lean_apply_2(v_h__2_603_, v_head_607_, v_x_601_);
            return v___x_608_;
        } else {
            let mut v_head_609_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_610_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_611_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_606_);
            lean_dec(v_h__2_603_);
            v_head_609_ = lean_ctor_get(v_x_600_, 0);
            lean_inc(v_head_609_);
            lean_dec_ref_known(v_x_600_, 2);
            v_head_610_ = lean_ctor_get(v_tail_606_, 0);
            lean_inc(v_head_610_);
            v_tail_611_ = lean_ctor_get(v_tail_606_, 1);
            lean_inc(v_tail_611_);
            lean_dec_ref_known(v_tail_606_, 2);
            v___x_612_ = lean_apply_4(v_h__3_604_, v_head_609_, v_head_610_, v_tail_611_, v_x_601_);
            return v___x_612_;
        }
    }
}
pub unsafe fn l_List_zipIdxLE___redArg(
    mut v_le_613_: *mut LeanObject,
    mut v_a_614_: *mut LeanObject,
    mut v_b_615_: *mut LeanObject,
) -> u8 {
    let mut v_fst_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    v_fst_616_ = lean_ctor_get(v_a_614_, 0);
    lean_inc_n(v_fst_616_, 2);
    v_snd_617_ = lean_ctor_get(v_a_614_, 1);
    lean_inc(v_snd_617_);
    lean_dec_ref(v_a_614_);
    v_fst_618_ = lean_ctor_get(v_b_615_, 0);
    lean_inc_n(v_fst_618_, 2);
    v_snd_619_ = lean_ctor_get(v_b_615_, 1);
    lean_inc(v_snd_619_);
    lean_dec_ref(v_b_615_);
    lean_inc_ref(v_le_613_);
    v___x_620_ = lean_apply_2(v_le_613_, v_fst_616_, v_fst_618_);
    v___x_621_ = (lean_unbox(v___x_620_) as u8);
    if v___x_621_ == 0 {
        let mut v___x_622_: u8 = 0;
        lean_dec(v_snd_619_);
        lean_dec(v_fst_618_);
        lean_dec(v_snd_617_);
        lean_dec(v_fst_616_);
        lean_dec_ref(v_le_613_);
        v___x_622_ = (lean_unbox(v___x_620_) as u8);
        return v___x_622_;
    } else {
        let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_624_: u8 = 0;
        v___x_623_ = lean_apply_2(v_le_613_, v_fst_618_, v_fst_616_);
        v___x_624_ = (lean_unbox(v___x_623_) as u8);
        if v___x_624_ == 0 {
            let mut v___x_625_: u8 = 0;
            lean_dec(v_snd_619_);
            lean_dec(v_snd_617_);
            v___x_625_ = (lean_unbox(v___x_620_) as u8);
            return v___x_625_;
        } else {
            let mut v___x_626_: u8 = 0;
            v___x_626_ = lean_nat_dec_le(v_snd_617_, v_snd_619_);
            lean_dec(v_snd_619_);
            lean_dec(v_snd_617_);
            return v___x_626_;
        }
    }
}
pub unsafe fn l_List_zipIdxLE___redArg___boxed(
    mut v_le_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
    mut v_b_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_630_: u8 = 0;
    let mut v_r_631_: *mut LeanObject = core::ptr::null_mut();
    v_res_630_ = l_List_zipIdxLE___redArg(v_le_627_, v_a_628_, v_b_629_);
    v_r_631_ = lean_box((v_res_630_) as usize);
    return v_r_631_;
}
pub unsafe fn l_List_zipIdxLE(
    mut v_00_u03b1_632_: *mut LeanObject,
    mut v_le_633_: *mut LeanObject,
    mut v_a_634_: *mut LeanObject,
    mut v_b_635_: *mut LeanObject,
) -> u8 {
    let mut v___x_636_: u8 = 0;
    v___x_636_ = l_List_zipIdxLE___redArg(v_le_633_, v_a_634_, v_b_635_);
    return v___x_636_;
}
pub unsafe fn l_List_zipIdxLE___boxed(
    mut v_00_u03b1_637_: *mut LeanObject,
    mut v_le_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_b_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_641_: u8 = 0;
    let mut v_r_642_: *mut LeanObject = core::ptr::null_mut();
    v_res_641_ = l_List_zipIdxLE(v_00_u03b1_637_, v_le_638_, v_a_639_, v_b_640_);
    v_r_642_ = lean_box((v_res_641_) as usize);
    return v_r_642_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Sort_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_List_Sort_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_merge___auto__1 = _init_l_List_merge___auto__1();
    lean_mark_persistent(l_List_merge___auto__1);
    l_List_mergeSort___auto__1 = _init_l_List_mergeSort___auto__1();
    lean_mark_persistent(l_List_mergeSort___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Sort_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Sort_Basic(builtin);
}
