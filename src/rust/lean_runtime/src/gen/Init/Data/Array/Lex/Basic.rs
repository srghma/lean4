// Lean compiler output
// Module: Init.Data.Array.Lex.Basic
// Imports: Init.Data.Range.Polymorphic.RangeIterator Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Nat Init.Omega
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Range::Polymorphic::RangeIterator::{
    initialize_Init_Data_Range_Polymorphic_RangeIterator,
    runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Array_lex___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__3_value) as *mut LeanObject;
static l_Array_lex___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_lex___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Array_lex___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__6_value) as *mut LeanObject;
static l_Array_lex___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_lex___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__10_value) as *mut LeanObject;
static l_Array_lex___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_lex___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__10_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Array_lex___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__14_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Array_lex___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__15_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l_Array_lex___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__15_value) as *mut LeanObject;
static l_Array_lex___auto__1___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Array_lex___auto__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__15_value) as *mut LeanObject,
        7932075773091973500 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__17_value: LeanStringObject<15> = LeanStringObject {
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
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l_Array_lex___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__17_value) as *mut LeanObject;
static l_Array_lex___auto__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Array_lex___auto__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__17_value) as *mut LeanObject,
        7306243862518720553 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__19_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_Array_lex___auto__1___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__19_value) as *mut LeanObject;
static mut l_Array_lex___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__22_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l_Array_lex___auto__1___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__22_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__23_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__22_value) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__23_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__24_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0],
};
static mut l_Array_lex___auto__1___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__24_value) as *mut LeanObject;
static mut l_Array_lex___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__27: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__29: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__30: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__31: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__32: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__33_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 60, 95, 0],
};
static mut l_Array_lex___auto__1___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__33_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__34_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__33_value) as *mut LeanObject,
        6883052497475924672 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__34_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__35_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 100, 111, 116, 0],
};
static mut l_Array_lex___auto__1___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__35_value) as *mut LeanObject;
static l_Array_lex___auto__1___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__36_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_lex___auto__1___closed__36_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Array_lex___auto__1___closed__36_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_lex___auto__1___closed__35_value) as *mut LeanObject,
        6167508377434939095 as *mut LeanObject,
    ],
};
static mut l_Array_lex___auto__1___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value) as *mut LeanObject;
pub static l_Array_lex___auto__1___closed__37_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 1,
    m_data: [194, 183, 0],
};
static mut l_Array_lex___auto__1___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__37_value) as *mut LeanObject;
static mut l_Array_lex___auto__1___closed__38_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__38: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__39_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__39: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__40_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__40: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__41_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__41: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__42_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__42: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__43_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [60, 0],
};
static mut l_Array_lex___auto__1___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__43_value) as *mut LeanObject;
static mut l_Array_lex___auto__1___closed__44_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__44: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__45_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__45: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__46_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__46: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__47_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__47: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__48_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__48: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__49_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_Array_lex___auto__1___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__49_value) as *mut LeanObject;
static mut l_Array_lex___auto__1___closed__50_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__50: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__51_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__51: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__52_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__52: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__53_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__53: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__54_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__54: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__55_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__55: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__56_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__56: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__57_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__57: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__58_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__58: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__59_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__59: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__60_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_lex___auto__1___closed__60: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_lex___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_lex___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Array_lex___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_lex___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Array_lex___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ = l_Array_lex___auto__1___closed__10;
    v___x_267_ = l_Lean_mkAtom(v___x_266_);
    return v___x_267_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    v___x_268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__12_once),
        _init_l_Array_lex___auto__1___closed__12,
    );
    v___x_269_ = l_Array_lex___auto__1___closed__5;
    v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
    return v___x_270_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    v___x_285_ = l_Array_lex___auto__1___closed__19;
    v___x_286_ = l_Lean_mkAtom(v___x_285_);
    return v___x_286_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    v___x_287_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__20_once),
        _init_l_Array_lex___auto__1___closed__20,
    );
    v___x_288_ = l_Array_lex___auto__1___closed__5;
    v___x_289_ = lean_array_push(v___x_288_, v___x_287_);
    return v___x_289_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    v___x_294_ = l_Array_lex___auto__1___closed__24;
    v___x_295_ = lean_string_utf8_byte_size(v___x_294_);
    return v___x_295_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    v___x_296_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__25_once),
        _init_l_Array_lex___auto__1___closed__25,
    );
    v___x_297_ = lean_unsigned_to_nat(0);
    v___x_298_ = l_Array_lex___auto__1___closed__24;
    v___x_299_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_299_, 0, v___x_298_);
    lean_ctor_set(v___x_299_, 1, v___x_297_);
    lean_ctor_set(v___x_299_, 2, v___x_296_);
    return v___x_299_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    v___x_300_ = lean_box(0);
    v___x_301_ = lean_box(0);
    v___x_302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__26_once),
        _init_l_Array_lex___auto__1___closed__26,
    );
    v___x_303_ = lean_box(2);
    v___x_304_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_304_, 0, v___x_303_);
    lean_ctor_set(v___x_304_, 1, v___x_302_);
    lean_ctor_set(v___x_304_, 2, v___x_301_);
    lean_ctor_set(v___x_304_, 3, v___x_300_);
    return v___x_304_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    v___x_305_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__27_once),
        _init_l_Array_lex___auto__1___closed__27,
    );
    v___x_306_ = l_Array_lex___auto__1___closed__5;
    v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
    return v___x_307_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__29() -> *mut LeanObject {
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    v___x_308_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__28_once),
        _init_l_Array_lex___auto__1___closed__28,
    );
    v___x_309_ = l_Array_lex___auto__1___closed__23;
    v___x_310_ = lean_box(2);
    v___x_311_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_311_, 0, v___x_310_);
    lean_ctor_set(v___x_311_, 1, v___x_309_);
    lean_ctor_set(v___x_311_, 2, v___x_308_);
    return v___x_311_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__30() -> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29_once),
        _init_l_Array_lex___auto__1___closed__29,
    );
    v___x_313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__21_once),
        _init_l_Array_lex___auto__1___closed__21,
    );
    v___x_314_ = lean_array_push(v___x_313_, v___x_312_);
    return v___x_314_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__31() -> *mut LeanObject {
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_315_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__30_once),
        _init_l_Array_lex___auto__1___closed__30,
    );
    v___x_316_ = l_Array_lex___auto__1___closed__18;
    v___x_317_ = lean_box(2);
    v___x_318_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_318_, 0, v___x_317_);
    lean_ctor_set(v___x_318_, 1, v___x_316_);
    lean_ctor_set(v___x_318_, 2, v___x_315_);
    return v___x_318_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__32() -> *mut LeanObject {
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    v___x_319_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__31_once),
        _init_l_Array_lex___auto__1___closed__31,
    );
    v___x_320_ = l_Array_lex___auto__1___closed__5;
    v___x_321_ = lean_array_push(v___x_320_, v___x_319_);
    return v___x_321_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__38() -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Array_lex___auto__1___closed__37;
    v___x_333_ = l_Lean_mkAtom(v___x_332_);
    return v___x_333_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__39() -> *mut LeanObject {
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___x_334_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__38_once),
        _init_l_Array_lex___auto__1___closed__38,
    );
    v___x_335_ = l_Array_lex___auto__1___closed__5;
    v___x_336_ = lean_array_push(v___x_335_, v___x_334_);
    return v___x_336_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__40() -> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29_once),
        _init_l_Array_lex___auto__1___closed__29,
    );
    v___x_338_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__39_once),
        _init_l_Array_lex___auto__1___closed__39,
    );
    v___x_339_ = lean_array_push(v___x_338_, v___x_337_);
    return v___x_339_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__41() -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__40_once),
        _init_l_Array_lex___auto__1___closed__40,
    );
    v___x_341_ = l_Array_lex___auto__1___closed__36;
    v___x_342_ = lean_box(2);
    v___x_343_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_343_, 0, v___x_342_);
    lean_ctor_set(v___x_343_, 1, v___x_341_);
    lean_ctor_set(v___x_343_, 2, v___x_340_);
    return v___x_343_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__42() -> *mut LeanObject {
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    v___x_344_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41_once),
        _init_l_Array_lex___auto__1___closed__41,
    );
    v___x_345_ = l_Array_lex___auto__1___closed__5;
    v___x_346_ = lean_array_push(v___x_345_, v___x_344_);
    return v___x_346_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__44() -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ = l_Array_lex___auto__1___closed__43;
    v___x_349_ = l_Lean_mkAtom(v___x_348_);
    return v___x_349_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__45() -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__44_once),
        _init_l_Array_lex___auto__1___closed__44,
    );
    v___x_351_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__42_once),
        _init_l_Array_lex___auto__1___closed__42,
    );
    v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__46() -> *mut LeanObject {
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v___x_353_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41_once),
        _init_l_Array_lex___auto__1___closed__41,
    );
    v___x_354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__45_once),
        _init_l_Array_lex___auto__1___closed__45,
    );
    v___x_355_ = lean_array_push(v___x_354_, v___x_353_);
    return v___x_355_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__47() -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__46_once),
        _init_l_Array_lex___auto__1___closed__46,
    );
    v___x_357_ = l_Array_lex___auto__1___closed__34;
    v___x_358_ = lean_box(2);
    v___x_359_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_359_, 0, v___x_358_);
    lean_ctor_set(v___x_359_, 1, v___x_357_);
    lean_ctor_set(v___x_359_, 2, v___x_356_);
    return v___x_359_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__48() -> *mut LeanObject {
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v___x_360_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__47_once),
        _init_l_Array_lex___auto__1___closed__47,
    );
    v___x_361_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__32_once),
        _init_l_Array_lex___auto__1___closed__32,
    );
    v___x_362_ = lean_array_push(v___x_361_, v___x_360_);
    return v___x_362_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__50() -> *mut LeanObject {
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Array_lex___auto__1___closed__49;
    v___x_365_ = l_Lean_mkAtom(v___x_364_);
    return v___x_365_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__51() -> *mut LeanObject {
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    v___x_366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__50_once),
        _init_l_Array_lex___auto__1___closed__50,
    );
    v___x_367_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__48_once),
        _init_l_Array_lex___auto__1___closed__48,
    );
    v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
    return v___x_368_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__52() -> *mut LeanObject {
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    v___x_369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__51_once),
        _init_l_Array_lex___auto__1___closed__51,
    );
    v___x_370_ = l_Array_lex___auto__1___closed__16;
    v___x_371_ = lean_box(2);
    v___x_372_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_372_, 0, v___x_371_);
    lean_ctor_set(v___x_372_, 1, v___x_370_);
    lean_ctor_set(v___x_372_, 2, v___x_369_);
    return v___x_372_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__53() -> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    v___x_373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__52_once),
        _init_l_Array_lex___auto__1___closed__52,
    );
    v___x_374_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__13_once),
        _init_l_Array_lex___auto__1___closed__13,
    );
    v___x_375_ = lean_array_push(v___x_374_, v___x_373_);
    return v___x_375_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__54() -> *mut LeanObject {
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__53_once),
        _init_l_Array_lex___auto__1___closed__53,
    );
    v___x_377_ = l_Array_lex___auto__1___closed__11;
    v___x_378_ = lean_box(2);
    v___x_379_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_379_, 0, v___x_378_);
    lean_ctor_set(v___x_379_, 1, v___x_377_);
    lean_ctor_set(v___x_379_, 2, v___x_376_);
    return v___x_379_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__55() -> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__54_once),
        _init_l_Array_lex___auto__1___closed__54,
    );
    v___x_381_ = l_Array_lex___auto__1___closed__5;
    v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
    return v___x_382_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__56() -> *mut LeanObject {
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v___x_383_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__55_once),
        _init_l_Array_lex___auto__1___closed__55,
    );
    v___x_384_ = l_Array_lex___auto__1___closed__9;
    v___x_385_ = lean_box(2);
    v___x_386_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_386_, 0, v___x_385_);
    lean_ctor_set(v___x_386_, 1, v___x_384_);
    lean_ctor_set(v___x_386_, 2, v___x_383_);
    return v___x_386_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__57() -> *mut LeanObject {
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__56_once),
        _init_l_Array_lex___auto__1___closed__56,
    );
    v___x_388_ = l_Array_lex___auto__1___closed__5;
    v___x_389_ = lean_array_push(v___x_388_, v___x_387_);
    return v___x_389_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__58() -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__57_once),
        _init_l_Array_lex___auto__1___closed__57,
    );
    v___x_391_ = l_Array_lex___auto__1___closed__7;
    v___x_392_ = lean_box(2);
    v___x_393_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_393_, 0, v___x_392_);
    lean_ctor_set(v___x_393_, 1, v___x_391_);
    lean_ctor_set(v___x_393_, 2, v___x_390_);
    return v___x_393_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__59() -> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__58_once),
        _init_l_Array_lex___auto__1___closed__58,
    );
    v___x_395_ = l_Array_lex___auto__1___closed__5;
    v___x_396_ = lean_array_push(v___x_395_, v___x_394_);
    return v___x_396_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__60() -> *mut LeanObject {
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    v___x_397_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__59),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__59_once),
        _init_l_Array_lex___auto__1___closed__59,
    );
    v___x_398_ = l_Array_lex___auto__1___closed__4;
    v___x_399_ = lean_box(2);
    v___x_400_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_400_, 0, v___x_399_);
    lean_ctor_set(v___x_400_, 1, v___x_398_);
    lean_ctor_set(v___x_400_, 2, v___x_397_);
    return v___x_400_;
}
pub unsafe fn _init_l_Array_lex___auto__1() -> *mut LeanObject {
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__60),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__60_once),
        _init_l_Array_lex___auto__1___closed__60,
    );
    return v___x_401_;
}
pub unsafe fn l_Array_lex___redArg___lam__0(
    mut v___y_402_: *mut LeanObject,
    mut v_as_403_: *mut LeanObject,
    mut v_bs_404_: *mut LeanObject,
    mut v_lt_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
    mut v___x_407_: *mut LeanObject,
    mut v___x_408_: *mut LeanObject,
    mut v_next_409_: *mut LeanObject,
    mut v_acc_410_: *mut LeanObject,
    mut v_h_411_: *mut LeanObject,
    mut v_G_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_413_: u8 = 0;
    v___x_413_ = lean_nat_dec_lt(v_next_409_, v___y_402_);
    if v___x_413_ == 0 {
        lean_dec_ref(v_G_412_);
        lean_dec_ref(v___x_408_);
        lean_dec_ref(v_inst_406_);
        lean_dec_ref(v_lt_405_);
        lean_inc_ref(v_acc_410_);
        return v_acc_410_;
    } else {
        let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_417_: u8 = 0;
        v___x_414_ = lean_array_fget_borrowed(v_as_403_, v_next_409_);
        v___x_415_ = lean_array_fget_borrowed(v_bs_404_, v_next_409_);
        lean_inc(v___x_415_);
        lean_inc(v___x_414_);
        v___x_416_ = lean_apply_2(v_lt_405_, v___x_414_, v___x_415_);
        v___x_417_ = (lean_unbox(v___x_416_) as u8);
        if v___x_417_ == 0 {
            let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_419_: u8 = 0;
            lean_inc(v___x_415_);
            lean_inc(v___x_414_);
            v___x_418_ = lean_apply_2(v_inst_406_, v___x_414_, v___x_415_);
            v___x_419_ = (lean_unbox(v___x_418_) as u8);
            if v___x_419_ == 0 {
                let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_G_412_);
                lean_dec_ref(v___x_408_);
                v___x_420_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_420_, 0, v___x_416_);
                v___x_421_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_421_, 0, v___x_420_);
                lean_ctor_set(v___x_421_, 1, v___x_407_);
                return v___x_421_;
            } else {
                let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
                v___x_422_ = lean_unsigned_to_nat(1);
                v___x_423_ = lean_nat_add(v_next_409_, v___x_422_);
                v___x_424_ =
                    lean_apply_4(v_G_412_, v___x_423_, v___x_408_, lean_box(0), lean_box(0));
                return v___x_424_;
            }
        } else {
            let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_G_412_);
            lean_dec_ref(v___x_408_);
            lean_dec_ref(v_inst_406_);
            v___x_425_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_425_, 0, v___x_416_);
            v___x_426_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_426_, 0, v___x_425_);
            lean_ctor_set(v___x_426_, 1, v___x_407_);
            return v___x_426_;
        }
    }
}
pub unsafe fn l_Array_lex___redArg___lam__0___boxed(
    mut v___y_427_: *mut LeanObject,
    mut v_as_428_: *mut LeanObject,
    mut v_bs_429_: *mut LeanObject,
    mut v_lt_430_: *mut LeanObject,
    mut v_inst_431_: *mut LeanObject,
    mut v___x_432_: *mut LeanObject,
    mut v___x_433_: *mut LeanObject,
    mut v_next_434_: *mut LeanObject,
    mut v_acc_435_: *mut LeanObject,
    mut v_h_436_: *mut LeanObject,
    mut v_G_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_438_: *mut LeanObject = core::ptr::null_mut();
    v_res_438_ = l_Array_lex___redArg___lam__0(
        v___y_427_,
        v_as_428_,
        v_bs_429_,
        v_lt_430_,
        v_inst_431_,
        v___x_432_,
        v___x_433_,
        v_next_434_,
        v_acc_435_,
        v_h_436_,
        v_G_437_,
    );
    lean_dec_ref(v_acc_435_);
    lean_dec(v_next_434_);
    lean_dec_ref(v_bs_429_);
    lean_dec_ref(v_as_428_);
    lean_dec(v___y_427_);
    return v_res_438_;
}
pub unsafe fn l_Array_lex___redArg(
    mut v_inst_442_: *mut LeanObject,
    mut v_as_443_: *mut LeanObject,
    mut v_bs_444_: *mut LeanObject,
    mut v_lt_445_: *mut LeanObject,
) -> u8 {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    let mut v_val_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v___x_459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_446_ = lean_unsigned_to_nat(0);
                v___x_447_ = lean_array_get_size(v_as_443_);
                v___x_448_ = lean_array_get_size(v_bs_444_);
                v___x_459_ = lean_nat_dec_le(v___x_447_, v___x_448_);
                if v___x_459_ == 0 {
                    v___y_450_ = v___x_448_;
                    state = 1;
                    continue;
                } else {
                    v___y_450_ = v___x_447_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_451_ = lean_box(0);
                v___x_452_ = l_Array_lex___redArg___closed__0;
                v___f_453_ = lean_alloc_closure(
                    l_Array_lex___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                lean_closure_set(v___f_453_, 0, v___y_450_);
                lean_closure_set(v___f_453_, 1, v_as_443_);
                lean_closure_set(v___f_453_, 2, v_bs_444_);
                lean_closure_set(v___f_453_, 3, v_lt_445_);
                lean_closure_set(v___f_453_, 4, v_inst_442_);
                lean_closure_set(v___f_453_, 5, v___x_451_);
                lean_closure_set(v___f_453_, 6, v___x_452_);
                v___x_454_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_453_,
                    v___x_446_,
                    v___x_452_,
                    lean_box(0),
                );
                v_fst_455_ = lean_ctor_get(v___x_454_, 0);
                lean_inc(v_fst_455_);
                lean_dec(v___x_454_);
                if lean_obj_tag(v_fst_455_) == 0 {
                    v___x_456_ = lean_nat_dec_lt(v___x_447_, v___x_448_);
                    return v___x_456_;
                } else {
                    v_val_457_ = lean_ctor_get(v_fst_455_, 0);
                    lean_inc(v_val_457_);
                    lean_dec_ref_known(v_fst_455_, 1);
                    v___x_458_ = (lean_unbox(v_val_457_) as u8);
                    lean_dec(v_val_457_);
                    return v___x_458_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_lex___redArg___boxed(
    mut v_inst_460_: *mut LeanObject,
    mut v_as_461_: *mut LeanObject,
    mut v_bs_462_: *mut LeanObject,
    mut v_lt_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_464_: u8 = 0;
    let mut v_r_465_: *mut LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Array_lex___redArg(v_inst_460_, v_as_461_, v_bs_462_, v_lt_463_);
    v_r_465_ = lean_box((v_res_464_) as usize);
    return v_r_465_;
}
pub unsafe fn l_Array_lex(
    mut v_00_u03b1_466_: *mut LeanObject,
    mut v_inst_467_: *mut LeanObject,
    mut v_as_468_: *mut LeanObject,
    mut v_bs_469_: *mut LeanObject,
    mut v_lt_470_: *mut LeanObject,
) -> u8 {
    let mut v___x_471_: u8 = 0;
    v___x_471_ = l_Array_lex___redArg(v_inst_467_, v_as_468_, v_bs_469_, v_lt_470_);
    return v___x_471_;
}
pub unsafe fn l_Array_lex___boxed(
    mut v_00_u03b1_472_: *mut LeanObject,
    mut v_inst_473_: *mut LeanObject,
    mut v_as_474_: *mut LeanObject,
    mut v_bs_475_: *mut LeanObject,
    mut v_lt_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_477_: u8 = 0;
    let mut v_r_478_: *mut LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Array_lex(
        v_00_u03b1_472_,
        v_inst_473_,
        v_as_474_,
        v_bs_475_,
        v_lt_476_,
    );
    v_r_478_ = lean_box((v_res_477_) as usize);
    return v_r_478_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Lex_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Array_Lex_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_lex___auto__1 = _init_l_Array_lex___auto__1();
    lean_mark_persistent(l_Array_lex___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Lex_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Lex_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Lex_Basic(builtin);
}
