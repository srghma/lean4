// Lean compiler output
// Module: Init.Data.Array.QSort.Basic
// Imports: Init.Data.Vector.Basic Init.Data.Ord.Basic Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_shiftr, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
pub static l_Array_qpartition___auto__1___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__3_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Array_qpartition___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__6_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__8_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__10_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qpartition___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14893461734720614794 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Array_qpartition___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qpartition___auto__1___closed__14_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qpartition___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__15_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__15_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__15_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            3488656302031949961 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Array_qpartition___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
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
static mut l_Array_qsort___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__0_value) as *mut leanh::LeanObject;
static l_Array_qsort___auto__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Array_qsort___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__5_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__5_value) as *mut leanh::LeanObject;
static l_Array_qsort___auto__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__5_value)
                as *mut leanh::LeanObject,
            7932075773091973500 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__7_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__7_value) as *mut leanh::LeanObject;
static l_Array_qsort___auto__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__7_value)
                as *mut leanh::LeanObject,
            7306243862518720553 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__9_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__9_value) as *mut leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__12_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__13_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__12_value)
                as *mut leanh::LeanObject,
            9871775667037945883 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__14_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__23_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__24_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__23_value)
                as *mut leanh::LeanObject,
            6883052497475924672 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__25_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__25_value)
        as *mut leanh::LeanObject;
static l_Array_qsort___auto__1___closed__26_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__26_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__26_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__26_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__25_value)
                as *mut leanh::LeanObject,
            6167508377434939095 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__27_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__31_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__33_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__35_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__39_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Array_qsort___auto__1___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__39_value)
        as *mut leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__43_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__43: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__45: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__46_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__46: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__47_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__47: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__48_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__48: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__49_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__49: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__50_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__50: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_qsort___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Array_qpartition___auto__1___closed__10;
    v___x_548_ = l_Lean_mkAtom(v___x_547_);
    return v___x_548_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_549_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__12_once),
        _init_l_Array_qpartition___auto__1___closed__12,
    );
    v___x_550_ = l_Array_qpartition___auto__1___closed__5;
    v___x_551_ = lean_array_push(v___x_550_, v___x_549_);
    return v___x_551_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = l_Array_qpartition___auto__1___closed__16;
    v___x_563_ = l_Array_qpartition___auto__1___closed__5;
    v___x_564_ = lean_array_push(v___x_563_, v___x_562_);
    return v___x_564_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__17_once),
        _init_l_Array_qpartition___auto__1___closed__17,
    );
    v___x_566_ = l_Array_qpartition___auto__1___closed__15;
    v___x_567_ = leanh::lean_box(2);
    v___x_568_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    leanh::lean_ctor_set(v___x_568_, 1, v___x_566_);
    leanh::lean_ctor_set(v___x_568_, 2, v___x_565_);
    return v___x_568_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__18_once),
        _init_l_Array_qpartition___auto__1___closed__18,
    );
    v___x_570_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__13_once),
        _init_l_Array_qpartition___auto__1___closed__13,
    );
    v___x_571_ = lean_array_push(v___x_570_, v___x_569_);
    return v___x_571_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__19_once),
        _init_l_Array_qpartition___auto__1___closed__19,
    );
    v___x_573_ = l_Array_qpartition___auto__1___closed__11;
    v___x_574_ = leanh::lean_box(2);
    v___x_575_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_575_, 0, v___x_574_);
    leanh::lean_ctor_set(v___x_575_, 1, v___x_573_);
    leanh::lean_ctor_set(v___x_575_, 2, v___x_572_);
    return v___x_575_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_576_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__20_once),
        _init_l_Array_qpartition___auto__1___closed__20,
    );
    v___x_577_ = l_Array_qpartition___auto__1___closed__5;
    v___x_578_ = lean_array_push(v___x_577_, v___x_576_);
    return v___x_578_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__21_once),
        _init_l_Array_qpartition___auto__1___closed__21,
    );
    v___x_580_ = l_Array_qpartition___auto__1___closed__9;
    v___x_581_ = leanh::lean_box(2);
    v___x_582_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_582_, 0, v___x_581_);
    leanh::lean_ctor_set(v___x_582_, 1, v___x_580_);
    leanh::lean_ctor_set(v___x_582_, 2, v___x_579_);
    return v___x_582_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_583_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__22_once),
        _init_l_Array_qpartition___auto__1___closed__22,
    );
    v___x_584_ = l_Array_qpartition___auto__1___closed__5;
    v___x_585_ = lean_array_push(v___x_584_, v___x_583_);
    return v___x_585_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__23_once),
        _init_l_Array_qpartition___auto__1___closed__23,
    );
    v___x_587_ = l_Array_qpartition___auto__1___closed__7;
    v___x_588_ = leanh::lean_box(2);
    v___x_589_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_589_, 0, v___x_588_);
    leanh::lean_ctor_set(v___x_589_, 1, v___x_587_);
    leanh::lean_ctor_set(v___x_589_, 2, v___x_586_);
    return v___x_589_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__24_once),
        _init_l_Array_qpartition___auto__1___closed__24,
    );
    v___x_591_ = l_Array_qpartition___auto__1___closed__5;
    v___x_592_ = lean_array_push(v___x_591_, v___x_590_);
    return v___x_592_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_593_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__25_once),
        _init_l_Array_qpartition___auto__1___closed__25,
    );
    v___x_594_ = l_Array_qpartition___auto__1___closed__4;
    v___x_595_ = leanh::lean_box(2);
    v___x_596_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_596_, 0, v___x_595_);
    leanh::lean_ctor_set(v___x_596_, 1, v___x_594_);
    leanh::lean_ctor_set(v___x_596_, 2, v___x_593_);
    return v___x_596_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_597_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_597_;
}
pub unsafe fn _init_l_Array_qpartition___auto__3() -> *mut leanh::LeanObject {
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_598_;
}
pub unsafe fn _init_l_Array_qpartition___auto__5() -> *mut leanh::LeanObject {
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_599_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_599_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2()
-> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_600_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4()
-> *mut leanh::LeanObject {
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_601_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6()
-> *mut leanh::LeanObject {
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_602_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
    mut v_lt_603_: *mut leanh::LeanObject,
    mut v_hi_604_: *mut leanh::LeanObject,
    mut v_pivot_605_: *mut leanh::LeanObject,
    mut v_as_606_: *mut leanh::LeanObject,
    mut v_i_607_: *mut leanh::LeanObject,
    mut v_k_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_609_ = lean_nat_dec_lt(v_k_608_, v_hi_604_);
                if v___x_609_ == 0 {
                    leanh::lean_dec(v_k_608_);
                    leanh::lean_dec(v_pivot_605_);
                    leanh::lean_dec_ref(v_lt_603_);
                    v___x_610_ = lean_array_fswap(v_as_606_, v_i_607_, v_hi_604_);
                    v___x_611_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_611_, 0, v_i_607_);
                    leanh::lean_ctor_set(v___x_611_, 1, v___x_610_);
                    return v___x_611_;
                } else {
                    v___x_612_ = lean_array_fget_borrowed(v_as_606_, v_k_608_);
                    leanh::lean_inc_ref(v_lt_603_);
                    leanh::lean_inc(v_pivot_605_);
                    leanh::lean_inc(v___x_612_);
                    v___x_613_ = leanh::lean_apply_2(v_lt_603_, v___x_612_, v_pivot_605_);
                    v___x_614_ = (leanh::lean_unbox(v___x_613_) as u8);
                    if v___x_614_ == 0 {
                        v___x_615_ = leanh::lean_unsigned_to_nat(1);
                        v___x_616_ = lean_nat_add(v_k_608_, v___x_615_);
                        leanh::lean_dec(v_k_608_);
                        v_k_608_ = v___x_616_;
                        state = 0;
                        continue;
                    } else {
                        v___x_618_ = lean_array_fswap(v_as_606_, v_i_607_, v_k_608_);
                        v___x_619_ = leanh::lean_unsigned_to_nat(1);
                        v___x_620_ = lean_nat_add(v_i_607_, v___x_619_);
                        leanh::lean_dec(v_i_607_);
                        v___x_621_ = lean_nat_add(v_k_608_, v___x_619_);
                        leanh::lean_dec(v_k_608_);
                        v_as_606_ = v___x_618_;
                        v_i_607_ = v___x_620_;
                        v_k_608_ = v___x_621_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg___boxed(
    mut v_lt_623_: *mut leanh::LeanObject,
    mut v_hi_624_: *mut leanh::LeanObject,
    mut v_pivot_625_: *mut leanh::LeanObject,
    mut v_as_626_: *mut leanh::LeanObject,
    mut v_i_627_: *mut leanh::LeanObject,
    mut v_k_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
        v_lt_623_,
        v_hi_624_,
        v_pivot_625_,
        v_as_626_,
        v_i_627_,
        v_k_628_,
    );
    leanh::lean_dec(v_hi_624_);
    return v_res_629_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(
    mut v_00_u03b1_630_: *mut leanh::LeanObject,
    mut v_n_631_: *mut leanh::LeanObject,
    mut v_lt_632_: *mut leanh::LeanObject,
    mut v_lo_633_: *mut leanh::LeanObject,
    mut v_hi_634_: *mut leanh::LeanObject,
    mut v_hhi_635_: *mut leanh::LeanObject,
    mut v_pivot_636_: *mut leanh::LeanObject,
    mut v_as_637_: *mut leanh::LeanObject,
    mut v_i_638_: *mut leanh::LeanObject,
    mut v_k_639_: *mut leanh::LeanObject,
    mut v_ilo_640_: *mut leanh::LeanObject,
    mut v_ik_641_: *mut leanh::LeanObject,
    mut v_w_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
        v_lt_632_,
        v_hi_634_,
        v_pivot_636_,
        v_as_637_,
        v_i_638_,
        v_k_639_,
    );
    return v___x_643_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___boxed(
    mut v_00_u03b1_644_: *mut leanh::LeanObject,
    mut v_n_645_: *mut leanh::LeanObject,
    mut v_lt_646_: *mut leanh::LeanObject,
    mut v_lo_647_: *mut leanh::LeanObject,
    mut v_hi_648_: *mut leanh::LeanObject,
    mut v_hhi_649_: *mut leanh::LeanObject,
    mut v_pivot_650_: *mut leanh::LeanObject,
    mut v_as_651_: *mut leanh::LeanObject,
    mut v_i_652_: *mut leanh::LeanObject,
    mut v_k_653_: *mut leanh::LeanObject,
    mut v_ilo_654_: *mut leanh::LeanObject,
    mut v_ik_655_: *mut leanh::LeanObject,
    mut v_w_656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(
        v_00_u03b1_644_,
        v_n_645_,
        v_lt_646_,
        v_lo_647_,
        v_hi_648_,
        v_hhi_649_,
        v_pivot_650_,
        v_as_651_,
        v_i_652_,
        v_k_653_,
        v_ilo_654_,
        v_ik_655_,
        v_w_656_,
    );
    leanh::lean_dec(v_hi_648_);
    leanh::lean_dec(v_lo_647_);
    leanh::lean_dec(v_n_645_);
    return v_res_657_;
}
pub unsafe fn l_Array_qpartition___redArg(
    mut v_as_658_: *mut leanh::LeanObject,
    mut v_lt_659_: *mut leanh::LeanObject,
    mut v_lo_660_: *mut leanh::LeanObject,
    mut v_hi_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_666_ = lean_nat_add(v_lo_660_, v_hi_661_);
                v___x_667_ = leanh::lean_unsigned_to_nat(1);
                v_mid_668_ = lean_nat_shiftr(v___x_666_, v___x_667_);
                leanh::lean_dec(v___x_666_);
                v___x_683_ = lean_array_fget_borrowed(v_as_658_, v_mid_668_);
                v___x_684_ = lean_array_fget_borrowed(v_as_658_, v_lo_660_);
                leanh::lean_inc_ref(v_lt_659_);
                leanh::lean_inc(v___x_684_);
                leanh::lean_inc(v___x_683_);
                v___x_685_ = leanh::lean_apply_2(v_lt_659_, v___x_683_, v___x_684_);
                v___x_686_ = (leanh::lean_unbox(v___x_685_) as u8);
                if v___x_686_ == 0 {
                    v___y_677_ = v_as_658_;
                    state = 3;
                    continue;
                } else {
                    v___x_687_ = lean_array_fswap(v_as_658_, v_lo_660_, v_mid_668_);
                    v___y_677_ = v___x_687_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_pivot_664_ = lean_array_fget(v___y_663_, v_hi_661_);
                leanh::lean_inc(v_lo_660_);
                v___x_665_ =
                    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
                        v_lt_659_,
                        v_hi_661_,
                        v_pivot_664_,
                        v___y_663_,
                        v_lo_660_,
                        v_lo_660_,
                    );
                return v___x_665_;
            }
            2 => {
                v___x_671_ = lean_array_fget_borrowed(v___y_670_, v_mid_668_);
                v___x_672_ = lean_array_fget_borrowed(v___y_670_, v_hi_661_);
                leanh::lean_inc_ref(v_lt_659_);
                leanh::lean_inc(v___x_672_);
                leanh::lean_inc(v___x_671_);
                v___x_673_ = leanh::lean_apply_2(v_lt_659_, v___x_671_, v___x_672_);
                v___x_674_ = (leanh::lean_unbox(v___x_673_) as u8);
                if v___x_674_ == 0 {
                    leanh::lean_dec(v_mid_668_);
                    v___y_663_ = v___y_670_;
                    state = 1;
                    continue;
                } else {
                    v___x_675_ = lean_array_fswap(v___y_670_, v_mid_668_, v_hi_661_);
                    leanh::lean_dec(v_mid_668_);
                    v___y_663_ = v___x_675_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_678_ = lean_array_fget_borrowed(v___y_677_, v_hi_661_);
                v___x_679_ = lean_array_fget_borrowed(v___y_677_, v_lo_660_);
                leanh::lean_inc_ref(v_lt_659_);
                leanh::lean_inc(v___x_679_);
                leanh::lean_inc(v___x_678_);
                v___x_680_ = leanh::lean_apply_2(v_lt_659_, v___x_678_, v___x_679_);
                v___x_681_ = (leanh::lean_unbox(v___x_680_) as u8);
                if v___x_681_ == 0 {
                    v___y_670_ = v___y_677_;
                    state = 2;
                    continue;
                } else {
                    v___x_682_ = lean_array_fswap(v___y_677_, v_lo_660_, v_hi_661_);
                    v___y_670_ = v___x_682_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qpartition___redArg___boxed(
    mut v_as_688_: *mut leanh::LeanObject,
    mut v_lt_689_: *mut leanh::LeanObject,
    mut v_lo_690_: *mut leanh::LeanObject,
    mut v_hi_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Array_qpartition___redArg(v_as_688_, v_lt_689_, v_lo_690_, v_hi_691_);
    leanh::lean_dec(v_hi_691_);
    return v_res_692_;
}
pub unsafe fn l_Array_qpartition(
    mut v_00_u03b1_693_: *mut leanh::LeanObject,
    mut v_n_694_: *mut leanh::LeanObject,
    mut v_as_695_: *mut leanh::LeanObject,
    mut v_lt_696_: *mut leanh::LeanObject,
    mut v_lo_697_: *mut leanh::LeanObject,
    mut v_hi_698_: *mut leanh::LeanObject,
    mut v_w_699_: *mut leanh::LeanObject,
    mut v_hlo_700_: *mut leanh::LeanObject,
    mut v_hhi_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: u8 = 0;
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_706_ = lean_nat_add(v_lo_697_, v_hi_698_);
                v___x_707_ = leanh::lean_unsigned_to_nat(1);
                v_mid_708_ = lean_nat_shiftr(v___x_706_, v___x_707_);
                leanh::lean_dec(v___x_706_);
                v___x_723_ = lean_array_fget_borrowed(v_as_695_, v_mid_708_);
                v___x_724_ = lean_array_fget_borrowed(v_as_695_, v_lo_697_);
                leanh::lean_inc_ref(v_lt_696_);
                leanh::lean_inc(v___x_724_);
                leanh::lean_inc(v___x_723_);
                v___x_725_ = leanh::lean_apply_2(v_lt_696_, v___x_723_, v___x_724_);
                v___x_726_ = (leanh::lean_unbox(v___x_725_) as u8);
                if v___x_726_ == 0 {
                    v___y_717_ = v_as_695_;
                    state = 3;
                    continue;
                } else {
                    v___x_727_ = lean_array_fswap(v_as_695_, v_lo_697_, v_mid_708_);
                    v___y_717_ = v___x_727_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_pivot_704_ = lean_array_fget(v___y_703_, v_hi_698_);
                leanh::lean_inc(v_lo_697_);
                v___x_705_ =
                    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
                        v_lt_696_,
                        v_hi_698_,
                        v_pivot_704_,
                        v___y_703_,
                        v_lo_697_,
                        v_lo_697_,
                    );
                return v___x_705_;
            }
            2 => {
                v___x_711_ = lean_array_fget_borrowed(v___y_710_, v_mid_708_);
                v___x_712_ = lean_array_fget_borrowed(v___y_710_, v_hi_698_);
                leanh::lean_inc_ref(v_lt_696_);
                leanh::lean_inc(v___x_712_);
                leanh::lean_inc(v___x_711_);
                v___x_713_ = leanh::lean_apply_2(v_lt_696_, v___x_711_, v___x_712_);
                v___x_714_ = (leanh::lean_unbox(v___x_713_) as u8);
                if v___x_714_ == 0 {
                    leanh::lean_dec(v_mid_708_);
                    v___y_703_ = v___y_710_;
                    state = 1;
                    continue;
                } else {
                    v___x_715_ = lean_array_fswap(v___y_710_, v_mid_708_, v_hi_698_);
                    leanh::lean_dec(v_mid_708_);
                    v___y_703_ = v___x_715_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_718_ = lean_array_fget_borrowed(v___y_717_, v_hi_698_);
                v___x_719_ = lean_array_fget_borrowed(v___y_717_, v_lo_697_);
                leanh::lean_inc_ref(v_lt_696_);
                leanh::lean_inc(v___x_719_);
                leanh::lean_inc(v___x_718_);
                v___x_720_ = leanh::lean_apply_2(v_lt_696_, v___x_718_, v___x_719_);
                v___x_721_ = (leanh::lean_unbox(v___x_720_) as u8);
                if v___x_721_ == 0 {
                    v___y_710_ = v___y_717_;
                    state = 2;
                    continue;
                } else {
                    v___x_722_ = lean_array_fswap(v___y_717_, v_lo_697_, v_hi_698_);
                    v___y_710_ = v___x_722_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qpartition___boxed(
    mut v_00_u03b1_728_: *mut leanh::LeanObject,
    mut v_n_729_: *mut leanh::LeanObject,
    mut v_as_730_: *mut leanh::LeanObject,
    mut v_lt_731_: *mut leanh::LeanObject,
    mut v_lo_732_: *mut leanh::LeanObject,
    mut v_hi_733_: *mut leanh::LeanObject,
    mut v_w_734_: *mut leanh::LeanObject,
    mut v_hlo_735_: *mut leanh::LeanObject,
    mut v_hhi_736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ = l_Array_qpartition(
        v_00_u03b1_728_,
        v_n_729_,
        v_as_730_,
        v_lt_731_,
        v_lo_732_,
        v_hi_733_,
        v_w_734_,
        v_hlo_735_,
        v_hhi_736_,
    );
    leanh::lean_dec(v_hi_733_);
    leanh::lean_dec(v_n_729_);
    return v_res_737_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Array_qsort___auto__1___closed__0;
    v___x_745_ = l_Lean_mkAtom(v___x_744_);
    return v___x_745_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__2),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__2_once),
        _init_l_Array_qsort___auto__1___closed__2,
    );
    v___x_747_ = l_Array_qpartition___auto__1___closed__5;
    v___x_748_ = lean_array_push(v___x_747_, v___x_746_);
    return v___x_748_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_763_ = l_Array_qsort___auto__1___closed__9;
    v___x_764_ = l_Lean_mkAtom(v___x_763_);
    return v___x_764_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__10_once),
        _init_l_Array_qsort___auto__1___closed__10,
    );
    v___x_766_ = l_Array_qpartition___auto__1___closed__5;
    v___x_767_ = lean_array_push(v___x_766_, v___x_765_);
    return v___x_767_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Array_qsort___auto__1___closed__14;
    v___x_773_ = lean_string_utf8_byte_size(v___x_772_);
    return v___x_773_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__15_once),
        _init_l_Array_qsort___auto__1___closed__15,
    );
    v___x_775_ = leanh::lean_unsigned_to_nat(0);
    v___x_776_ = l_Array_qsort___auto__1___closed__14;
    v___x_777_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_777_, 0, v___x_776_);
    leanh::lean_ctor_set(v___x_777_, 1, v___x_775_);
    leanh::lean_ctor_set(v___x_777_, 2, v___x_774_);
    return v___x_777_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_778_ = leanh::lean_box(0);
    v___x_779_ = leanh::lean_box(0);
    v___x_780_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__16_once),
        _init_l_Array_qsort___auto__1___closed__16,
    );
    v___x_781_ = leanh::lean_box(2);
    v___x_782_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_782_, 0, v___x_781_);
    leanh::lean_ctor_set(v___x_782_, 1, v___x_780_);
    leanh::lean_ctor_set(v___x_782_, 2, v___x_779_);
    leanh::lean_ctor_set(v___x_782_, 3, v___x_778_);
    return v___x_782_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_783_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__17_once),
        _init_l_Array_qsort___auto__1___closed__17,
    );
    v___x_784_ = l_Array_qpartition___auto__1___closed__5;
    v___x_785_ = lean_array_push(v___x_784_, v___x_783_);
    return v___x_785_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_786_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__18_once),
        _init_l_Array_qsort___auto__1___closed__18,
    );
    v___x_787_ = l_Array_qsort___auto__1___closed__13;
    v___x_788_ = leanh::lean_box(2);
    v___x_789_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_789_, 0, v___x_788_);
    leanh::lean_ctor_set(v___x_789_, 1, v___x_787_);
    leanh::lean_ctor_set(v___x_789_, 2, v___x_786_);
    return v___x_789_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19_once),
        _init_l_Array_qsort___auto__1___closed__19,
    );
    v___x_791_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__11_once),
        _init_l_Array_qsort___auto__1___closed__11,
    );
    v___x_792_ = lean_array_push(v___x_791_, v___x_790_);
    return v___x_792_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__20_once),
        _init_l_Array_qsort___auto__1___closed__20,
    );
    v___x_794_ = l_Array_qsort___auto__1___closed__8;
    v___x_795_ = leanh::lean_box(2);
    v___x_796_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_796_, 0, v___x_795_);
    leanh::lean_ctor_set(v___x_796_, 1, v___x_794_);
    leanh::lean_ctor_set(v___x_796_, 2, v___x_793_);
    return v___x_796_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__21_once),
        _init_l_Array_qsort___auto__1___closed__21,
    );
    v___x_798_ = l_Array_qpartition___auto__1___closed__5;
    v___x_799_ = lean_array_push(v___x_798_, v___x_797_);
    return v___x_799_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Array_qsort___auto__1___closed__27;
    v___x_811_ = l_Lean_mkAtom(v___x_810_);
    return v___x_811_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__28_once),
        _init_l_Array_qsort___auto__1___closed__28,
    );
    v___x_813_ = l_Array_qpartition___auto__1___closed__5;
    v___x_814_ = lean_array_push(v___x_813_, v___x_812_);
    return v___x_814_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__30() -> *mut leanh::LeanObject {
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19_once),
        _init_l_Array_qsort___auto__1___closed__19,
    );
    v___x_816_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__29_once),
        _init_l_Array_qsort___auto__1___closed__29,
    );
    v___x_817_ = lean_array_push(v___x_816_, v___x_815_);
    return v___x_817_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__31() -> *mut leanh::LeanObject {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__30_once),
        _init_l_Array_qsort___auto__1___closed__30,
    );
    v___x_819_ = l_Array_qsort___auto__1___closed__26;
    v___x_820_ = leanh::lean_box(2);
    v___x_821_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_821_, 0, v___x_820_);
    leanh::lean_ctor_set(v___x_821_, 1, v___x_819_);
    leanh::lean_ctor_set(v___x_821_, 2, v___x_818_);
    return v___x_821_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__32() -> *mut leanh::LeanObject {
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_822_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31_once),
        _init_l_Array_qsort___auto__1___closed__31,
    );
    v___x_823_ = l_Array_qpartition___auto__1___closed__5;
    v___x_824_ = lean_array_push(v___x_823_, v___x_822_);
    return v___x_824_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__34() -> *mut leanh::LeanObject {
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = l_Array_qsort___auto__1___closed__33;
    v___x_827_ = l_Lean_mkAtom(v___x_826_);
    return v___x_827_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__35() -> *mut leanh::LeanObject {
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__34_once),
        _init_l_Array_qsort___auto__1___closed__34,
    );
    v___x_829_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__32_once),
        _init_l_Array_qsort___auto__1___closed__32,
    );
    v___x_830_ = lean_array_push(v___x_829_, v___x_828_);
    return v___x_830_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__36() -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31_once),
        _init_l_Array_qsort___auto__1___closed__31,
    );
    v___x_832_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__35),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__35_once),
        _init_l_Array_qsort___auto__1___closed__35,
    );
    v___x_833_ = lean_array_push(v___x_832_, v___x_831_);
    return v___x_833_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__37() -> *mut leanh::LeanObject {
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__36_once),
        _init_l_Array_qsort___auto__1___closed__36,
    );
    v___x_835_ = l_Array_qsort___auto__1___closed__24;
    v___x_836_ = leanh::lean_box(2);
    v___x_837_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_837_, 0, v___x_836_);
    leanh::lean_ctor_set(v___x_837_, 1, v___x_835_);
    leanh::lean_ctor_set(v___x_837_, 2, v___x_834_);
    return v___x_837_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__38() -> *mut leanh::LeanObject {
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__37),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__37_once),
        _init_l_Array_qsort___auto__1___closed__37,
    );
    v___x_839_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__22_once),
        _init_l_Array_qsort___auto__1___closed__22,
    );
    v___x_840_ = lean_array_push(v___x_839_, v___x_838_);
    return v___x_840_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__40() -> *mut leanh::LeanObject {
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_842_ = l_Array_qsort___auto__1___closed__39;
    v___x_843_ = l_Lean_mkAtom(v___x_842_);
    return v___x_843_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__41() -> *mut leanh::LeanObject {
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__40_once),
        _init_l_Array_qsort___auto__1___closed__40,
    );
    v___x_845_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__38_once),
        _init_l_Array_qsort___auto__1___closed__38,
    );
    v___x_846_ = lean_array_push(v___x_845_, v___x_844_);
    return v___x_846_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__42() -> *mut leanh::LeanObject {
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__41_once),
        _init_l_Array_qsort___auto__1___closed__41,
    );
    v___x_848_ = l_Array_qsort___auto__1___closed__6;
    v___x_849_ = leanh::lean_box(2);
    v___x_850_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_850_, 0, v___x_849_);
    leanh::lean_ctor_set(v___x_850_, 1, v___x_848_);
    leanh::lean_ctor_set(v___x_850_, 2, v___x_847_);
    return v___x_850_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__43() -> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__42_once),
        _init_l_Array_qsort___auto__1___closed__42,
    );
    v___x_852_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__3),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__3_once),
        _init_l_Array_qsort___auto__1___closed__3,
    );
    v___x_853_ = lean_array_push(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__44() -> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__43_once),
        _init_l_Array_qsort___auto__1___closed__43,
    );
    v___x_855_ = l_Array_qsort___auto__1___closed__1;
    v___x_856_ = leanh::lean_box(2);
    v___x_857_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_857_, 0, v___x_856_);
    leanh::lean_ctor_set(v___x_857_, 1, v___x_855_);
    leanh::lean_ctor_set(v___x_857_, 2, v___x_854_);
    return v___x_857_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__45() -> *mut leanh::LeanObject {
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__44_once),
        _init_l_Array_qsort___auto__1___closed__44,
    );
    v___x_859_ = l_Array_qpartition___auto__1___closed__5;
    v___x_860_ = lean_array_push(v___x_859_, v___x_858_);
    return v___x_860_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__46() -> *mut leanh::LeanObject {
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__45_once),
        _init_l_Array_qsort___auto__1___closed__45,
    );
    v___x_862_ = l_Array_qpartition___auto__1___closed__9;
    v___x_863_ = leanh::lean_box(2);
    v___x_864_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_864_, 0, v___x_863_);
    leanh::lean_ctor_set(v___x_864_, 1, v___x_862_);
    leanh::lean_ctor_set(v___x_864_, 2, v___x_861_);
    return v___x_864_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__47() -> *mut leanh::LeanObject {
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__46_once),
        _init_l_Array_qsort___auto__1___closed__46,
    );
    v___x_866_ = l_Array_qpartition___auto__1___closed__5;
    v___x_867_ = lean_array_push(v___x_866_, v___x_865_);
    return v___x_867_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__48() -> *mut leanh::LeanObject {
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__47_once),
        _init_l_Array_qsort___auto__1___closed__47,
    );
    v___x_869_ = l_Array_qpartition___auto__1___closed__7;
    v___x_870_ = leanh::lean_box(2);
    v___x_871_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_871_, 0, v___x_870_);
    leanh::lean_ctor_set(v___x_871_, 1, v___x_869_);
    leanh::lean_ctor_set(v___x_871_, 2, v___x_868_);
    return v___x_871_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__49() -> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__48_once),
        _init_l_Array_qsort___auto__1___closed__48,
    );
    v___x_873_ = l_Array_qpartition___auto__1___closed__5;
    v___x_874_ = lean_array_push(v___x_873_, v___x_872_);
    return v___x_874_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__50() -> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__49),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__49_once),
        _init_l_Array_qsort___auto__1___closed__49,
    );
    v___x_876_ = l_Array_qpartition___auto__1___closed__4;
    v___x_877_ = leanh::lean_box(2);
    v___x_878_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_878_, 0, v___x_877_);
    leanh::lean_ctor_set(v___x_878_, 1, v___x_876_);
    leanh::lean_ctor_set(v___x_878_, 2, v___x_875_);
    return v___x_878_;
}
pub unsafe fn _init_l_Array_qsort___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__50_once),
        _init_l_Array_qsort___auto__1___closed__50,
    );
    return v___x_879_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2()
-> *mut leanh::LeanObject {
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_880_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4()
-> *mut leanh::LeanObject {
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_881_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6()
-> *mut leanh::LeanObject {
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_882_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
    mut v_lt_883_: *mut leanh::LeanObject,
    mut v_as_884_: *mut leanh::LeanObject,
    mut v_lo_885_: *mut leanh::LeanObject,
    mut v_hi_886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: u8 = 0;
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_898_ = lean_nat_dec_lt(v_lo_885_, v_hi_886_);
                if v___x_898_ == 0 {
                    leanh::lean_dec(v_lo_885_);
                    leanh::lean_dec_ref(v_lt_883_);
                    return v_as_884_;
                } else {
                    v___x_899_ = lean_nat_add(v_lo_885_, v_hi_886_);
                    v___x_900_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_901_ = lean_nat_shiftr(v___x_899_, v___x_900_);
                    leanh::lean_dec(v___x_899_);
                    v___x_916_ = lean_array_fget_borrowed(v_as_884_, v_mid_901_);
                    v___x_917_ = lean_array_fget_borrowed(v_as_884_, v_lo_885_);
                    leanh::lean_inc_ref(v_lt_883_);
                    leanh::lean_inc(v___x_917_);
                    leanh::lean_inc(v___x_916_);
                    v___x_918_ = leanh::lean_apply_2(v_lt_883_, v___x_916_, v___x_917_);
                    v___x_919_ = (leanh::lean_unbox(v___x_918_) as u8);
                    if v___x_919_ == 0 {
                        v___y_910_ = v_as_884_;
                        state = 3;
                        continue;
                    } else {
                        v___x_920_ = lean_array_fswap(v_as_884_, v_lo_885_, v_mid_901_);
                        v___y_910_ = v___x_920_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_889_ = lean_array_fget(v___y_888_, v_hi_886_);
                leanh::lean_inc_n(v_lo_885_, 2);
                leanh::lean_inc_ref(v_lt_883_);
                v___x_890_ =
                    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
                        v_lt_883_,
                        v_hi_886_,
                        v_pivot_889_,
                        v___y_888_,
                        v_lo_885_,
                        v_lo_885_,
                    );
                v_fst_891_ = leanh::lean_ctor_get(v___x_890_, 0);
                leanh::lean_inc(v_fst_891_);
                v_snd_892_ = leanh::lean_ctor_get(v___x_890_, 1);
                leanh::lean_inc(v_snd_892_);
                leanh::lean_dec_ref(v___x_890_);
                v___x_893_ = lean_nat_dec_le(v_hi_886_, v_fst_891_);
                if v___x_893_ == 0 {
                    leanh::lean_inc_ref(v_lt_883_);
                    v___x_894_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_883_, v_snd_892_, v_lo_885_, v_fst_891_,
                        );
                    v___x_895_ = leanh::lean_unsigned_to_nat(1);
                    v___x_896_ = lean_nat_add(v_fst_891_, v___x_895_);
                    leanh::lean_dec(v_fst_891_);
                    v_as_884_ = v___x_894_;
                    v_lo_885_ = v___x_896_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_891_);
                    leanh::lean_dec(v_lo_885_);
                    leanh::lean_dec_ref(v_lt_883_);
                    return v_snd_892_;
                }
            }
            2 => {
                v___x_904_ = lean_array_fget_borrowed(v___y_903_, v_mid_901_);
                v___x_905_ = lean_array_fget_borrowed(v___y_903_, v_hi_886_);
                leanh::lean_inc_ref(v_lt_883_);
                leanh::lean_inc(v___x_905_);
                leanh::lean_inc(v___x_904_);
                v___x_906_ = leanh::lean_apply_2(v_lt_883_, v___x_904_, v___x_905_);
                v___x_907_ = (leanh::lean_unbox(v___x_906_) as u8);
                if v___x_907_ == 0 {
                    leanh::lean_dec(v_mid_901_);
                    v___y_888_ = v___y_903_;
                    state = 1;
                    continue;
                } else {
                    v___x_908_ = lean_array_fswap(v___y_903_, v_mid_901_, v_hi_886_);
                    leanh::lean_dec(v_mid_901_);
                    v___y_888_ = v___x_908_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_911_ = lean_array_fget_borrowed(v___y_910_, v_hi_886_);
                v___x_912_ = lean_array_fget_borrowed(v___y_910_, v_lo_885_);
                leanh::lean_inc_ref(v_lt_883_);
                leanh::lean_inc(v___x_912_);
                leanh::lean_inc(v___x_911_);
                v___x_913_ = leanh::lean_apply_2(v_lt_883_, v___x_911_, v___x_912_);
                v___x_914_ = (leanh::lean_unbox(v___x_913_) as u8);
                if v___x_914_ == 0 {
                    v___y_903_ = v___y_910_;
                    state = 2;
                    continue;
                } else {
                    v___x_915_ = lean_array_fswap(v___y_910_, v_lo_885_, v_hi_886_);
                    v___y_903_ = v___x_915_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg___boxed(
    mut v_lt_921_: *mut leanh::LeanObject,
    mut v_as_922_: *mut leanh::LeanObject,
    mut v_lo_923_: *mut leanh::LeanObject,
    mut v_hi_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
        v_lt_921_, v_as_922_, v_lo_923_, v_hi_924_,
    );
    leanh::lean_dec(v_hi_924_);
    return v_res_925_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
    mut v_00_u03b1_926_: *mut leanh::LeanObject,
    mut v_lt_927_: *mut leanh::LeanObject,
    mut v_n_928_: *mut leanh::LeanObject,
    mut v_as_929_: *mut leanh::LeanObject,
    mut v_lo_930_: *mut leanh::LeanObject,
    mut v_hi_931_: *mut leanh::LeanObject,
    mut v_w_932_: *mut leanh::LeanObject,
    mut v_hlo_933_: *mut leanh::LeanObject,
    mut v_hhi_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
        v_lt_927_, v_as_929_, v_lo_930_, v_hi_931_,
    );
    return v___x_935_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___boxed(
    mut v_00_u03b1_936_: *mut leanh::LeanObject,
    mut v_lt_937_: *mut leanh::LeanObject,
    mut v_n_938_: *mut leanh::LeanObject,
    mut v_as_939_: *mut leanh::LeanObject,
    mut v_lo_940_: *mut leanh::LeanObject,
    mut v_hi_941_: *mut leanh::LeanObject,
    mut v_w_942_: *mut leanh::LeanObject,
    mut v_hlo_943_: *mut leanh::LeanObject,
    mut v_hhi_944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
        v_00_u03b1_936_,
        v_lt_937_,
        v_n_938_,
        v_as_939_,
        v_lo_940_,
        v_hi_941_,
        v_w_942_,
        v_hlo_943_,
        v_hhi_944_,
    );
    leanh::lean_dec(v_hi_941_);
    leanh::lean_dec(v_n_938_);
    return v_res_945_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___redArg(
    mut v_x_946_: *mut leanh::LeanObject,
    mut v_h__1_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_948_ = leanh::lean_ctor_get(v_x_946_, 0);
    leanh::lean_inc(v_fst_948_);
    v_snd_949_ = leanh::lean_ctor_get(v_x_946_, 1);
    leanh::lean_inc(v_snd_949_);
    leanh::lean_dec_ref(v_x_946_);
    v___x_950_ = leanh::lean_apply_3(
        v_h__1_947_,
        v_fst_948_,
        leanh::lean_box(0),
        v_snd_949_,
    );
    return v___x_950_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(
    mut v_00_u03b1_951_: *mut leanh::LeanObject,
    mut v_n_952_: *mut leanh::LeanObject,
    mut v_lo_953_: *mut leanh::LeanObject,
    mut v_hi_954_: *mut leanh::LeanObject,
    mut v_motive_955_: *mut leanh::LeanObject,
    mut v_x_956_: *mut leanh::LeanObject,
    mut v_h__1_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_958_ = leanh::lean_ctor_get(v_x_956_, 0);
    leanh::lean_inc(v_fst_958_);
    v_snd_959_ = leanh::lean_ctor_get(v_x_956_, 1);
    leanh::lean_inc(v_snd_959_);
    leanh::lean_dec_ref(v_x_956_);
    v___x_960_ = leanh::lean_apply_3(
        v_h__1_957_,
        v_fst_958_,
        leanh::lean_box(0),
        v_snd_959_,
    );
    return v___x_960_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___boxed(
    mut v_00_u03b1_961_: *mut leanh::LeanObject,
    mut v_n_962_: *mut leanh::LeanObject,
    mut v_lo_963_: *mut leanh::LeanObject,
    mut v_hi_964_: *mut leanh::LeanObject,
    mut v_motive_965_: *mut leanh::LeanObject,
    mut v_x_966_: *mut leanh::LeanObject,
    mut v_h__1_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(
        v_00_u03b1_961_,
        v_n_962_,
        v_lo_963_,
        v_hi_964_,
        v_motive_965_,
        v_x_966_,
        v_h__1_967_,
    );
    leanh::lean_dec(v_hi_964_);
    leanh::lean_dec(v_lo_963_);
    leanh::lean_dec(v_n_962_);
    return v_res_968_;
}
pub unsafe fn l_Array_qsort___redArg(
    mut v_as_969_: *mut leanh::LeanObject,
    mut v_lt_970_: *mut leanh::LeanObject,
    mut v_lo_971_: *mut leanh::LeanObject,
    mut v_hi_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u8 = 0;
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_979_ = lean_array_get_size(v_as_969_);
                v___x_980_ = leanh::lean_unsigned_to_nat(0);
                v___x_981_ = lean_nat_dec_eq(v___x_979_, v___x_980_);
                if v___x_981_ == 0 {
                    v___x_982_ = leanh::lean_unsigned_to_nat(1);
                    v___x_983_ = lean_nat_sub(v___x_979_, v___x_982_);
                    v___x_987_ = lean_nat_dec_le(v_lo_971_, v___x_983_);
                    if v___x_987_ == 0 {
                        leanh::lean_dec(v_lo_971_);
                        leanh::lean_inc(v___x_983_);
                        v___y_985_ = v___x_983_;
                        state = 2;
                        continue;
                    } else {
                        v___y_985_ = v_lo_971_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_hi_972_);
                    leanh::lean_dec(v_lo_971_);
                    leanh::lean_dec_ref(v_lt_970_);
                    return v_as_969_;
                }
            }
            1 => {
                v___x_976_ = lean_nat_dec_le(v___y_974_, v___y_975_);
                if v___x_976_ == 0 {
                    leanh::lean_dec(v___y_975_);
                    leanh::lean_inc(v___y_974_);
                    v___x_977_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_970_, v_as_969_, v___y_974_, v___y_974_,
                        );
                    leanh::lean_dec(v___y_974_);
                    return v___x_977_;
                } else {
                    v___x_978_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_970_, v_as_969_, v___y_974_, v___y_975_,
                        );
                    leanh::lean_dec(v___y_975_);
                    return v___x_978_;
                }
            }
            2 => {
                v___x_986_ = lean_nat_dec_le(v_hi_972_, v___x_983_);
                if v___x_986_ == 0 {
                    leanh::lean_dec(v_hi_972_);
                    v___y_974_ = v___y_985_;
                    v___y_975_ = v___x_983_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_983_);
                    v___y_974_ = v___y_985_;
                    v___y_975_ = v_hi_972_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qsort(
    mut v_00_u03b1_988_: *mut leanh::LeanObject,
    mut v_as_989_: *mut leanh::LeanObject,
    mut v_lt_990_: *mut leanh::LeanObject,
    mut v_lo_991_: *mut leanh::LeanObject,
    mut v_hi_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: u8 = 0;
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_999_ = lean_array_get_size(v_as_989_);
                v___x_1000_ = leanh::lean_unsigned_to_nat(0);
                v___x_1001_ = lean_nat_dec_eq(v___x_999_, v___x_1000_);
                if v___x_1001_ == 0 {
                    v___x_1002_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1003_ = lean_nat_sub(v___x_999_, v___x_1002_);
                    v___x_1007_ = lean_nat_dec_le(v_lo_991_, v___x_1003_);
                    if v___x_1007_ == 0 {
                        leanh::lean_dec(v_lo_991_);
                        leanh::lean_inc(v___x_1003_);
                        v___y_1005_ = v___x_1003_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1005_ = v_lo_991_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_hi_992_);
                    leanh::lean_dec(v_lo_991_);
                    leanh::lean_dec_ref(v_lt_990_);
                    return v_as_989_;
                }
            }
            1 => {
                v___x_996_ = lean_nat_dec_le(v___y_994_, v___y_995_);
                if v___x_996_ == 0 {
                    leanh::lean_dec(v___y_995_);
                    leanh::lean_inc(v___y_994_);
                    v___x_997_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_990_, v_as_989_, v___y_994_, v___y_994_,
                        );
                    leanh::lean_dec(v___y_994_);
                    return v___x_997_;
                } else {
                    v___x_998_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_990_, v_as_989_, v___y_994_, v___y_995_,
                        );
                    leanh::lean_dec(v___y_995_);
                    return v___x_998_;
                }
            }
            2 => {
                v___x_1006_ = lean_nat_dec_le(v_hi_992_, v___x_1003_);
                if v___x_1006_ == 0 {
                    leanh::lean_dec(v_hi_992_);
                    v___y_994_ = v___y_1005_;
                    v___y_995_ = v___x_1003_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1003_);
                    v___y_994_ = v___y_1005_;
                    v___y_995_ = v_hi_992_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qsortOrd___redArg___lam__0(
    mut v_ord_1008_: *mut leanh::LeanObject,
    mut v___x_1009_: u8,
    mut v_x_1010_: *mut leanh::LeanObject,
    mut v_y_1011_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u8 = 0;
    v___x_1012_ = leanh::lean_apply_2(v_ord_1008_, v_x_1010_, v_y_1011_);
    v___x_1013_ = (leanh::lean_unbox(v___x_1012_) as u8);
    if v___x_1013_ == 0 {
        let mut v___x_1014_: u8 = 0;
        v___x_1014_ = 1;
        return v___x_1014_;
    } else {
        return v___x_1009_;
    }
}
pub unsafe fn l_Array_qsortOrd___redArg___lam__0___boxed(
    mut v_ord_1015_: *mut leanh::LeanObject,
    mut v___x_1016_: *mut leanh::LeanObject,
    mut v_x_1017_: *mut leanh::LeanObject,
    mut v_y_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_63__boxed_1019_: u8 = 0;
    let mut v_res_1020_: u8 = 0;
    let mut v_r_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_63__boxed_1019_ = (leanh::lean_unbox(v___x_1016_) as u8);
    v_res_1020_ = l_Array_qsortOrd___redArg___lam__0(
        v_ord_1015_,
        v___x_63__boxed_1019_,
        v_x_1017_,
        v_y_1018_,
    );
    v_r_1021_ = leanh::lean_box((v_res_1020_) as usize);
    return v_r_1021_;
}
pub unsafe fn l_Array_qsortOrd___redArg(
    mut v_ord_1022_: *mut leanh::LeanObject,
    mut v_xs_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1024_ = lean_array_get_size(v_xs_1023_);
                v___x_1025_ = leanh::lean_unsigned_to_nat(0);
                v___x_1026_ = lean_nat_dec_eq(v___x_1024_, v___x_1025_);
                if v___x_1026_ == 0 {
                    v___x_1027_ = leanh::lean_box((v___x_1026_) as usize);
                    v___f_1028_ = leanh::lean_alloc_closure(
                        l_Array_qsortOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1028_, 0, v_ord_1022_);
                    leanh::lean_closure_set(v___f_1028_, 1, v___x_1027_);
                    v___x_1029_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1030_ = lean_nat_sub(v___x_1024_, v___x_1029_);
                    v___x_1036_ = lean_nat_dec_le(v___x_1025_, v___x_1030_);
                    if v___x_1036_ == 0 {
                        leanh::lean_inc(v___x_1030_);
                        v___y_1032_ = v___x_1030_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1032_ = v___x_1025_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_ord_1022_);
                    return v_xs_1023_;
                }
            }
            1 => {
                v___x_1033_ = lean_nat_dec_le(v___y_1032_, v___x_1030_);
                if v___x_1033_ == 0 {
                    leanh::lean_dec(v___x_1030_);
                    leanh::lean_inc(v___y_1032_);
                    v___x_1034_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v___f_1028_,
                            v_xs_1023_,
                            v___y_1032_,
                            v___y_1032_,
                        );
                    leanh::lean_dec(v___y_1032_);
                    return v___x_1034_;
                } else {
                    v___x_1035_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v___f_1028_,
                            v_xs_1023_,
                            v___y_1032_,
                            v___x_1030_,
                        );
                    leanh::lean_dec(v___x_1030_);
                    return v___x_1035_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qsortOrd(
    mut v_00_u03b1_1037_: *mut leanh::LeanObject,
    mut v_ord_1038_: *mut leanh::LeanObject,
    mut v_xs_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_Array_qsortOrd___redArg(v_ord_1038_, v_xs_1039_);
    return v___x_1040_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_QSort_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_QSort_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_qpartition___auto__1 = _init_l_Array_qpartition___auto__1();
    leanh::lean_mark_persistent(l_Array_qpartition___auto__1);
    l_Array_qpartition___auto__3 = _init_l_Array_qpartition___auto__3();
    leanh::lean_mark_persistent(l_Array_qpartition___auto__3);
    l_Array_qpartition___auto__5 = _init_l_Array_qpartition___auto__5();
    leanh::lean_mark_persistent(l_Array_qpartition___auto__5);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6,
    );
    l_Array_qsort___auto__1 = _init_l_Array_qsort___auto__1();
    leanh::lean_mark_persistent(l_Array_qsort___auto__1);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_QSort_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_QSort_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_QSort_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_QSort_Basic(builtin);
}