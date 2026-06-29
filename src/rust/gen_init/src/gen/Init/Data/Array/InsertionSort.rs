// Lean compiler output
// Module: Init.Data.Array.InsertionSort
// Imports: Init.Data.Array.Basic
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_fswap, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
pub static l_Array_insertionSort___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Array_insertionSort___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Array_insertionSort___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Array_insertionSort___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
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
static mut l_Array_insertionSort___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Array_insertionSort___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_insertionSort___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Array_insertionSort___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
static mut l_Array_insertionSort___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Array_insertionSort___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_insertionSort___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Array_insertionSort___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Array_insertionSort___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_insertionSort___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_insertionSort___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_insertionSort___auto__1___closed__14_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Array_insertionSort___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__15_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Array_insertionSort___auto__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__16_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__16_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_insertionSort___auto__1___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__16_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__15_value)
                as *mut crate::leanh::LeanObject,
            7932075773091973500 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__17_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Array_insertionSort___auto__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__18_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__18_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_insertionSort___auto__1___closed__18_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__18_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__17_value)
                as *mut crate::leanh::LeanObject,
            7306243862518720553 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__19_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_insertionSort___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_insertionSort___auto__1___closed__22_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__23_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__22_value)
                as *mut crate::leanh::LeanObject,
            9871775667037945883 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__24_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__24_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_insertionSort___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_insertionSort___auto__1___closed__33_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__34_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__33_value)
                as *mut crate::leanh::LeanObject,
            6883052497475924672 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__35_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Array_insertionSort___auto__1___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__36_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_insertionSort___auto__1___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__36_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_insertionSort___auto__1___closed__36_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__36_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__35_value)
                as *mut crate::leanh::LeanObject,
            6167508377434939095 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_insertionSort___auto__1___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_insertionSort___auto__1___closed__37_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__37_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_insertionSort___auto__1___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__42_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_insertionSort___auto__1___closed__43_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_insertionSort___auto__1___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__46_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__47_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__48_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_insertionSort___auto__1___closed__49_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_insertionSort___auto__1___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_insertionSort___auto__1___closed__49_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_insertionSort___auto__1___closed__50_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__51_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__52_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__53_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__54_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__55_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__56_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__57_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__58_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__59_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_insertionSort___auto__1___closed__60_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_insertionSort___auto__1___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_insertionSort___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = l_Array_insertionSort___auto__1___closed__10;
    v___x_239_ = l_Lean_mkAtom(v___x_238_);
    return v___x_239_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__12_once),
        _init_l_Array_insertionSort___auto__1___closed__12,
    );
    v___x_241_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_242_ = lean_array_push(v___x_241_, v___x_240_);
    return v___x_242_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__20() -> *mut crate::leanh::LeanObject
{
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ = l_Array_insertionSort___auto__1___closed__19;
    v___x_258_ = l_Lean_mkAtom(v___x_257_);
    return v___x_258_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__21() -> *mut crate::leanh::LeanObject
{
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_259_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__20_once),
        _init_l_Array_insertionSort___auto__1___closed__20,
    );
    v___x_260_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_261_ = lean_array_push(v___x_260_, v___x_259_);
    return v___x_261_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__25() -> *mut crate::leanh::LeanObject
{
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = l_Array_insertionSort___auto__1___closed__24;
    v___x_267_ = lean_string_utf8_byte_size(v___x_266_);
    return v___x_267_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__26() -> *mut crate::leanh::LeanObject
{
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__25_once),
        _init_l_Array_insertionSort___auto__1___closed__25,
    );
    v___x_269_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_270_ = l_Array_insertionSort___auto__1___closed__24;
    v___x_271_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_271_, 0, v___x_270_);
    crate::leanh::lean_ctor_set(v___x_271_, 1, v___x_269_);
    crate::leanh::lean_ctor_set(v___x_271_, 2, v___x_268_);
    return v___x_271_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__27() -> *mut crate::leanh::LeanObject
{
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = crate::leanh::lean_box(0);
    v___x_273_ = crate::leanh::lean_box(0);
    v___x_274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__26_once),
        _init_l_Array_insertionSort___auto__1___closed__26,
    );
    v___x_275_ = crate::leanh::lean_box(2);
    v___x_276_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_276_, 0, v___x_275_);
    crate::leanh::lean_ctor_set(v___x_276_, 1, v___x_274_);
    crate::leanh::lean_ctor_set(v___x_276_, 2, v___x_273_);
    crate::leanh::lean_ctor_set(v___x_276_, 3, v___x_272_);
    return v___x_276_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__28() -> *mut crate::leanh::LeanObject
{
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__27_once),
        _init_l_Array_insertionSort___auto__1___closed__27,
    );
    v___x_278_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_279_ = lean_array_push(v___x_278_, v___x_277_);
    return v___x_279_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__29() -> *mut crate::leanh::LeanObject
{
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__28_once),
        _init_l_Array_insertionSort___auto__1___closed__28,
    );
    v___x_281_ = l_Array_insertionSort___auto__1___closed__23;
    v___x_282_ = crate::leanh::lean_box(2);
    v___x_283_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_283_, 0, v___x_282_);
    crate::leanh::lean_ctor_set(v___x_283_, 1, v___x_281_);
    crate::leanh::lean_ctor_set(v___x_283_, 2, v___x_280_);
    return v___x_283_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__30() -> *mut crate::leanh::LeanObject
{
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__29_once),
        _init_l_Array_insertionSort___auto__1___closed__29,
    );
    v___x_285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__21_once),
        _init_l_Array_insertionSort___auto__1___closed__21,
    );
    v___x_286_ = lean_array_push(v___x_285_, v___x_284_);
    return v___x_286_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__31() -> *mut crate::leanh::LeanObject
{
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__30_once),
        _init_l_Array_insertionSort___auto__1___closed__30,
    );
    v___x_288_ = l_Array_insertionSort___auto__1___closed__18;
    v___x_289_ = crate::leanh::lean_box(2);
    v___x_290_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_290_, 0, v___x_289_);
    crate::leanh::lean_ctor_set(v___x_290_, 1, v___x_288_);
    crate::leanh::lean_ctor_set(v___x_290_, 2, v___x_287_);
    return v___x_290_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__32() -> *mut crate::leanh::LeanObject
{
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__31_once),
        _init_l_Array_insertionSort___auto__1___closed__31,
    );
    v___x_292_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_293_ = lean_array_push(v___x_292_, v___x_291_);
    return v___x_293_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__38() -> *mut crate::leanh::LeanObject
{
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_304_ = l_Array_insertionSort___auto__1___closed__37;
    v___x_305_ = l_Lean_mkAtom(v___x_304_);
    return v___x_305_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__39() -> *mut crate::leanh::LeanObject
{
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_306_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__38_once),
        _init_l_Array_insertionSort___auto__1___closed__38,
    );
    v___x_307_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_308_ = lean_array_push(v___x_307_, v___x_306_);
    return v___x_308_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__40() -> *mut crate::leanh::LeanObject
{
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__29_once),
        _init_l_Array_insertionSort___auto__1___closed__29,
    );
    v___x_310_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__39_once),
        _init_l_Array_insertionSort___auto__1___closed__39,
    );
    v___x_311_ = lean_array_push(v___x_310_, v___x_309_);
    return v___x_311_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__41() -> *mut crate::leanh::LeanObject
{
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__40_once),
        _init_l_Array_insertionSort___auto__1___closed__40,
    );
    v___x_313_ = l_Array_insertionSort___auto__1___closed__36;
    v___x_314_ = crate::leanh::lean_box(2);
    v___x_315_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_314_);
    crate::leanh::lean_ctor_set(v___x_315_, 1, v___x_313_);
    crate::leanh::lean_ctor_set(v___x_315_, 2, v___x_312_);
    return v___x_315_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__42() -> *mut crate::leanh::LeanObject
{
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__41_once),
        _init_l_Array_insertionSort___auto__1___closed__41,
    );
    v___x_317_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_318_ = lean_array_push(v___x_317_, v___x_316_);
    return v___x_318_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__44() -> *mut crate::leanh::LeanObject
{
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_320_ = l_Array_insertionSort___auto__1___closed__43;
    v___x_321_ = l_Lean_mkAtom(v___x_320_);
    return v___x_321_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__45() -> *mut crate::leanh::LeanObject
{
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__44_once),
        _init_l_Array_insertionSort___auto__1___closed__44,
    );
    v___x_323_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__42_once),
        _init_l_Array_insertionSort___auto__1___closed__42,
    );
    v___x_324_ = lean_array_push(v___x_323_, v___x_322_);
    return v___x_324_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__46() -> *mut crate::leanh::LeanObject
{
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_325_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__41_once),
        _init_l_Array_insertionSort___auto__1___closed__41,
    );
    v___x_326_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__45_once),
        _init_l_Array_insertionSort___auto__1___closed__45,
    );
    v___x_327_ = lean_array_push(v___x_326_, v___x_325_);
    return v___x_327_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__47() -> *mut crate::leanh::LeanObject
{
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_328_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__46_once),
        _init_l_Array_insertionSort___auto__1___closed__46,
    );
    v___x_329_ = l_Array_insertionSort___auto__1___closed__34;
    v___x_330_ = crate::leanh::lean_box(2);
    v___x_331_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_331_, 0, v___x_330_);
    crate::leanh::lean_ctor_set(v___x_331_, 1, v___x_329_);
    crate::leanh::lean_ctor_set(v___x_331_, 2, v___x_328_);
    return v___x_331_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__48() -> *mut crate::leanh::LeanObject
{
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__47_once),
        _init_l_Array_insertionSort___auto__1___closed__47,
    );
    v___x_333_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__32_once),
        _init_l_Array_insertionSort___auto__1___closed__32,
    );
    v___x_334_ = lean_array_push(v___x_333_, v___x_332_);
    return v___x_334_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__50() -> *mut crate::leanh::LeanObject
{
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ = l_Array_insertionSort___auto__1___closed__49;
    v___x_337_ = l_Lean_mkAtom(v___x_336_);
    return v___x_337_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__51() -> *mut crate::leanh::LeanObject
{
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__50_once),
        _init_l_Array_insertionSort___auto__1___closed__50,
    );
    v___x_339_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__48_once),
        _init_l_Array_insertionSort___auto__1___closed__48,
    );
    v___x_340_ = lean_array_push(v___x_339_, v___x_338_);
    return v___x_340_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__52() -> *mut crate::leanh::LeanObject
{
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__51_once),
        _init_l_Array_insertionSort___auto__1___closed__51,
    );
    v___x_342_ = l_Array_insertionSort___auto__1___closed__16;
    v___x_343_ = crate::leanh::lean_box(2);
    v___x_344_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_344_, 0, v___x_343_);
    crate::leanh::lean_ctor_set(v___x_344_, 1, v___x_342_);
    crate::leanh::lean_ctor_set(v___x_344_, 2, v___x_341_);
    return v___x_344_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__53() -> *mut crate::leanh::LeanObject
{
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__52_once),
        _init_l_Array_insertionSort___auto__1___closed__52,
    );
    v___x_346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__13_once),
        _init_l_Array_insertionSort___auto__1___closed__13,
    );
    v___x_347_ = lean_array_push(v___x_346_, v___x_345_);
    return v___x_347_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__54() -> *mut crate::leanh::LeanObject
{
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__53_once),
        _init_l_Array_insertionSort___auto__1___closed__53,
    );
    v___x_349_ = l_Array_insertionSort___auto__1___closed__11;
    v___x_350_ = crate::leanh::lean_box(2);
    v___x_351_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_351_, 0, v___x_350_);
    crate::leanh::lean_ctor_set(v___x_351_, 1, v___x_349_);
    crate::leanh::lean_ctor_set(v___x_351_, 2, v___x_348_);
    return v___x_351_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__55() -> *mut crate::leanh::LeanObject
{
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_352_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__54_once),
        _init_l_Array_insertionSort___auto__1___closed__54,
    );
    v___x_353_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_354_ = lean_array_push(v___x_353_, v___x_352_);
    return v___x_354_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__56() -> *mut crate::leanh::LeanObject
{
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__55_once),
        _init_l_Array_insertionSort___auto__1___closed__55,
    );
    v___x_356_ = l_Array_insertionSort___auto__1___closed__9;
    v___x_357_ = crate::leanh::lean_box(2);
    v___x_358_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_358_, 0, v___x_357_);
    crate::leanh::lean_ctor_set(v___x_358_, 1, v___x_356_);
    crate::leanh::lean_ctor_set(v___x_358_, 2, v___x_355_);
    return v___x_358_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__57() -> *mut crate::leanh::LeanObject
{
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__56_once),
        _init_l_Array_insertionSort___auto__1___closed__56,
    );
    v___x_360_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_361_ = lean_array_push(v___x_360_, v___x_359_);
    return v___x_361_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__58() -> *mut crate::leanh::LeanObject
{
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__57_once),
        _init_l_Array_insertionSort___auto__1___closed__57,
    );
    v___x_363_ = l_Array_insertionSort___auto__1___closed__7;
    v___x_364_ = crate::leanh::lean_box(2);
    v___x_365_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_365_, 0, v___x_364_);
    crate::leanh::lean_ctor_set(v___x_365_, 1, v___x_363_);
    crate::leanh::lean_ctor_set(v___x_365_, 2, v___x_362_);
    return v___x_365_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__59() -> *mut crate::leanh::LeanObject
{
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__58_once),
        _init_l_Array_insertionSort___auto__1___closed__58,
    );
    v___x_367_ = l_Array_insertionSort___auto__1___closed__5;
    v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
    return v___x_368_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1___closed__60() -> *mut crate::leanh::LeanObject
{
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__59),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__59_once),
        _init_l_Array_insertionSort___auto__1___closed__59,
    );
    v___x_370_ = l_Array_insertionSort___auto__1___closed__4;
    v___x_371_ = crate::leanh::lean_box(2);
    v___x_372_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
    crate::leanh::lean_ctor_set(v___x_372_, 1, v___x_370_);
    crate::leanh::lean_ctor_set(v___x_372_, 2, v___x_369_);
    return v___x_372_;
}
pub unsafe fn _init_l_Array_insertionSort___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__60),
        core::ptr::addr_of_mut!(l_Array_insertionSort___auto__1___closed__60_once),
        _init_l_Array_insertionSort___auto__1___closed__60,
    );
    return v___x_373_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___redArg(
    mut v_lt_374_: *mut crate::leanh::LeanObject,
    mut v_xs_375_: *mut crate::leanh::LeanObject,
    mut v_j_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_378_: u8 = 0;
    let mut v_one_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: u8 = 0;
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_377_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_378_ = lean_nat_dec_eq(v_j_376_, v_zero_377_);
                if v_isZero_378_ == 1 {
                    crate::leanh::lean_dec(v_j_376_);
                    crate::leanh::lean_dec_ref(v_lt_374_);
                    return v_xs_375_;
                } else {
                    v_one_379_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_380_ = lean_nat_sub(v_j_376_, v_one_379_);
                    v___x_381_ = lean_array_fget_borrowed(v_xs_375_, v_j_376_);
                    v___x_382_ = lean_array_fget_borrowed(v_xs_375_, v_n_380_);
                    crate::leanh::lean_inc_ref(v_lt_374_);
                    crate::leanh::lean_inc(v___x_382_);
                    crate::leanh::lean_inc(v___x_381_);
                    v___x_383_ = crate::leanh::lean_apply_2(v_lt_374_, v___x_381_, v___x_382_);
                    v___x_384_ = (crate::leanh::lean_unbox(v___x_383_) as u8);
                    if v___x_384_ == 0 {
                        crate::leanh::lean_dec(v_n_380_);
                        crate::leanh::lean_dec(v_j_376_);
                        crate::leanh::lean_dec_ref(v_lt_374_);
                        return v_xs_375_;
                    } else {
                        v___x_385_ = lean_array_fswap(v_xs_375_, v_j_376_, v_n_380_);
                        crate::leanh::lean_dec(v_j_376_);
                        v_xs_375_ = v___x_385_;
                        v_j_376_ = v_n_380_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop(
    mut v_00_u03b1_387_: *mut crate::leanh::LeanObject,
    mut v_lt_388_: *mut crate::leanh::LeanObject,
    mut v_xs_389_: *mut crate::leanh::LeanObject,
    mut v_j_390_: *mut crate::leanh::LeanObject,
    mut v_h_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___redArg(
        v_lt_388_, v_xs_389_, v_j_390_,
    );
    return v___x_392_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___redArg(
    mut v_lt_393_: *mut crate::leanh::LeanObject,
    mut v_xs_394_: *mut crate::leanh::LeanObject,
    mut v_i_395_: *mut crate::leanh::LeanObject,
    mut v_fuel_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_398_: u8 = 0;
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: u8 = 0;
    let mut v_one_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_397_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_398_ = lean_nat_dec_eq(v_fuel_396_, v_zero_397_);
                if v_isZero_398_ == 1 {
                    crate::leanh::lean_dec(v_fuel_396_);
                    crate::leanh::lean_dec(v_i_395_);
                    crate::leanh::lean_dec_ref(v_lt_393_);
                    return v_xs_394_;
                } else {
                    v___x_399_ = lean_array_get_size(v_xs_394_);
                    v___x_400_ = lean_nat_dec_lt(v_i_395_, v___x_399_);
                    if v___x_400_ == 0 {
                        crate::leanh::lean_dec(v_fuel_396_);
                        crate::leanh::lean_dec(v_i_395_);
                        crate::leanh::lean_dec_ref(v_lt_393_);
                        return v_xs_394_;
                    } else {
                        v_one_401_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_402_ = lean_nat_sub(v_fuel_396_, v_one_401_);
                        crate::leanh::lean_dec(v_fuel_396_);
                        crate::leanh::lean_inc(v_i_395_);
                        crate::leanh::lean_inc_ref(v_lt_393_);
                        v___x_403_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___redArg(v_lt_393_, v_xs_394_, v_i_395_);
                        v___x_404_ = lean_nat_add(v_i_395_, v_one_401_);
                        crate::leanh::lean_dec(v_i_395_);
                        v_xs_394_ = v___x_403_;
                        v_i_395_ = v___x_404_;
                        v_fuel_396_ = v_n_402_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(
    mut v_00_u03b1_406_: *mut crate::leanh::LeanObject,
    mut v_lt_407_: *mut crate::leanh::LeanObject,
    mut v_xs_408_: *mut crate::leanh::LeanObject,
    mut v_i_409_: *mut crate::leanh::LeanObject,
    mut v_fuel_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___redArg(
        v_lt_407_,
        v_xs_408_,
        v_i_409_,
        v_fuel_410_,
    );
    return v___x_411_;
}
pub unsafe fn l_Array_insertionSort___redArg(
    mut v_xs_412_: *mut crate::leanh::LeanObject,
    mut v_lt_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_414_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_415_ = lean_array_get_size(v_xs_412_);
    v___x_416_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___redArg(
        v_lt_413_, v_xs_412_, v___x_414_, v___x_415_,
    );
    return v___x_416_;
}
pub unsafe fn l_Array_insertionSort(
    mut v_00_u03b1_417_: *mut crate::leanh::LeanObject,
    mut v_xs_418_: *mut crate::leanh::LeanObject,
    mut v_lt_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_421_ = lean_array_get_size(v_xs_418_);
    v___x_422_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___redArg(
        v_lt_419_, v_xs_418_, v___x_420_, v___x_421_,
    );
    return v___x_422_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_InsertionSort(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_InsertionSort(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_insertionSort___auto__1 = _init_l_Array_insertionSort___auto__1();
    crate::leanh::lean_mark_persistent(l_Array_insertionSort___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_InsertionSort(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_InsertionSort(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_InsertionSort(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_InsertionSort(builtin);
}
