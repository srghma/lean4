// Lean compiler output
// Module: Init.Data.Array.QSort.Basic
// Imports: Init.Data.Vector.Basic Init.Data.Ord.Basic Init.Omega
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_fswap;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
pub static l_Array_qpartition___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_qpartition___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Array_qpartition___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Array_qpartition___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Array_qpartition___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Array_qpartition___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_Array_qpartition___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_qpartition___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [111, 109, 101, 103, 97, 0],
    };
static mut l_Array_qpartition___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14893461734720614794 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_qpartition___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qpartition___auto__1___closed__14_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Array_qpartition___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Array_qpartition___auto__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qpartition___auto__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qpartition___auto__1___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            3488656302031949961 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qpartition___auto__1___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qpartition___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_qpartition___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qpartition___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__0_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Array_qsort___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Array_qsort___auto__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__4_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_qsort___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__5_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Array_qsort___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Array_qsort___auto__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__5_value)
                as *mut crate::leanh::LeanObject,
            7932075773091973500 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__7_value: crate::leanh::LeanStringObject<15> =
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
static mut l_Array_qsort___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Array_qsort___auto__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__7_value)
                as *mut crate::leanh::LeanObject,
            7306243862518720553 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__9_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Array_qsort___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__12_value: crate::leanh::LeanStringObject<12> =
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
static mut l_Array_qsort___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__12_value)
                as *mut crate::leanh::LeanObject,
            9871775667037945883 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__14_value: crate::leanh::LeanStringObject<12> =
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
static mut l_Array_qsort___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__23_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Array_qsort___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__24_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__23_value)
                as *mut crate::leanh::LeanObject,
            6883052497475924672 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__25_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_qsort___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Array_qsort___auto__1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_qsort___auto__1___closed__26_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_qsort___auto__1___closed__26_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_qsort___auto__1___closed__25_value)
                as *mut crate::leanh::LeanObject,
            6167508377434939095 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_qsort___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_qsort___auto__1___closed__27_value: crate::leanh::LeanStringObject<3> =
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
static mut l_Array_qsort___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__33_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Array_qsort___auto__1___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__35_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__39_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Array_qsort___auto__1___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__39_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_qsort___auto__1___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__42_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__43_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__46_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__47_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__48_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__49_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__50_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_qsort___auto__1___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_qsort___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Array_qpartition___auto__1___closed__10;
    v___x_548_ = l_Lean_mkAtom(v___x_547_);
    return v___x_548_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_549_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__12_once),
        _init_l_Array_qpartition___auto__1___closed__12,
    );
    v___x_550_ = l_Array_qpartition___auto__1___closed__5;
    v___x_551_ = lean_array_push(v___x_550_, v___x_549_);
    return v___x_551_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = l_Array_qpartition___auto__1___closed__16;
    v___x_563_ = l_Array_qpartition___auto__1___closed__5;
    v___x_564_ = lean_array_push(v___x_563_, v___x_562_);
    return v___x_564_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__17_once),
        _init_l_Array_qpartition___auto__1___closed__17,
    );
    v___x_566_ = l_Array_qpartition___auto__1___closed__15;
    v___x_567_ = crate::leanh::lean_box(2);
    v___x_568_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    crate::leanh::lean_ctor_set(v___x_568_, 1, v___x_566_);
    crate::leanh::lean_ctor_set(v___x_568_, 2, v___x_565_);
    return v___x_568_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__18_once),
        _init_l_Array_qpartition___auto__1___closed__18,
    );
    v___x_570_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__13_once),
        _init_l_Array_qpartition___auto__1___closed__13,
    );
    v___x_571_ = lean_array_push(v___x_570_, v___x_569_);
    return v___x_571_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__19_once),
        _init_l_Array_qpartition___auto__1___closed__19,
    );
    v___x_573_ = l_Array_qpartition___auto__1___closed__11;
    v___x_574_ = crate::leanh::lean_box(2);
    v___x_575_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_575_, 0, v___x_574_);
    crate::leanh::lean_ctor_set(v___x_575_, 1, v___x_573_);
    crate::leanh::lean_ctor_set(v___x_575_, 2, v___x_572_);
    return v___x_575_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_576_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__20_once),
        _init_l_Array_qpartition___auto__1___closed__20,
    );
    v___x_577_ = l_Array_qpartition___auto__1___closed__5;
    v___x_578_ = lean_array_push(v___x_577_, v___x_576_);
    return v___x_578_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__21_once),
        _init_l_Array_qpartition___auto__1___closed__21,
    );
    v___x_580_ = l_Array_qpartition___auto__1___closed__9;
    v___x_581_ = crate::leanh::lean_box(2);
    v___x_582_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_582_, 0, v___x_581_);
    crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_580_);
    crate::leanh::lean_ctor_set(v___x_582_, 2, v___x_579_);
    return v___x_582_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__22_once),
        _init_l_Array_qpartition___auto__1___closed__22,
    );
    v___x_584_ = l_Array_qpartition___auto__1___closed__5;
    v___x_585_ = lean_array_push(v___x_584_, v___x_583_);
    return v___x_585_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__23_once),
        _init_l_Array_qpartition___auto__1___closed__23,
    );
    v___x_587_ = l_Array_qpartition___auto__1___closed__7;
    v___x_588_ = crate::leanh::lean_box(2);
    v___x_589_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_589_, 0, v___x_588_);
    crate::leanh::lean_ctor_set(v___x_589_, 1, v___x_587_);
    crate::leanh::lean_ctor_set(v___x_589_, 2, v___x_586_);
    return v___x_589_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__24_once),
        _init_l_Array_qpartition___auto__1___closed__24,
    );
    v___x_591_ = l_Array_qpartition___auto__1___closed__5;
    v___x_592_ = lean_array_push(v___x_591_, v___x_590_);
    return v___x_592_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_593_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__25_once),
        _init_l_Array_qpartition___auto__1___closed__25,
    );
    v___x_594_ = l_Array_qpartition___auto__1___closed__4;
    v___x_595_ = crate::leanh::lean_box(2);
    v___x_596_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_596_, 0, v___x_595_);
    crate::leanh::lean_ctor_set(v___x_596_, 1, v___x_594_);
    crate::leanh::lean_ctor_set(v___x_596_, 2, v___x_593_);
    return v___x_596_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_597_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_597_;
}
pub unsafe fn _init_l_Array_qpartition___auto__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_598_;
}
pub unsafe fn _init_l_Array_qpartition___auto__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_599_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_599_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_600_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_601_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_602_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
    mut v_lt_603_: *mut crate::leanh::LeanObject,
    mut v_hi_604_: *mut crate::leanh::LeanObject,
    mut v_pivot_605_: *mut crate::leanh::LeanObject,
    mut v_as_606_: *mut crate::leanh::LeanObject,
    mut v_i_607_: *mut crate::leanh::LeanObject,
    mut v_k_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_609_ = lean_nat_dec_lt(v_k_608_, v_hi_604_);
                if v___x_609_ == 0 {
                    crate::leanh::lean_dec(v_k_608_);
                    crate::leanh::lean_dec(v_pivot_605_);
                    crate::leanh::lean_dec_ref(v_lt_603_);
                    v___x_610_ = lean_array_fswap(v_as_606_, v_i_607_, v_hi_604_);
                    v___x_611_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_611_, 0, v_i_607_);
                    crate::leanh::lean_ctor_set(v___x_611_, 1, v___x_610_);
                    return v___x_611_;
                } else {
                    v___x_612_ = lean_array_fget_borrowed(v_as_606_, v_k_608_);
                    crate::leanh::lean_inc_ref(v_lt_603_);
                    crate::leanh::lean_inc(v_pivot_605_);
                    crate::leanh::lean_inc(v___x_612_);
                    v___x_613_ = crate::leanh::lean_apply_2(v_lt_603_, v___x_612_, v_pivot_605_);
                    v___x_614_ = (crate::leanh::lean_unbox(v___x_613_) as u8);
                    if v___x_614_ == 0 {
                        v___x_615_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_616_ = lean_nat_add(v_k_608_, v___x_615_);
                        crate::leanh::lean_dec(v_k_608_);
                        v_k_608_ = v___x_616_;
                        state = 0;
                        continue;
                    } else {
                        v___x_618_ = lean_array_fswap(v_as_606_, v_i_607_, v_k_608_);
                        v___x_619_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_620_ = lean_nat_add(v_i_607_, v___x_619_);
                        crate::leanh::lean_dec(v_i_607_);
                        v___x_621_ = lean_nat_add(v_k_608_, v___x_619_);
                        crate::leanh::lean_dec(v_k_608_);
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
    mut v_lt_623_: *mut crate::leanh::LeanObject,
    mut v_hi_624_: *mut crate::leanh::LeanObject,
    mut v_pivot_625_: *mut crate::leanh::LeanObject,
    mut v_as_626_: *mut crate::leanh::LeanObject,
    mut v_i_627_: *mut crate::leanh::LeanObject,
    mut v_k_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
        v_lt_623_,
        v_hi_624_,
        v_pivot_625_,
        v_as_626_,
        v_i_627_,
        v_k_628_,
    );
    crate::leanh::lean_dec(v_hi_624_);
    return v_res_629_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(
    mut v_00_u03b1_630_: *mut crate::leanh::LeanObject,
    mut v_n_631_: *mut crate::leanh::LeanObject,
    mut v_lt_632_: *mut crate::leanh::LeanObject,
    mut v_lo_633_: *mut crate::leanh::LeanObject,
    mut v_hi_634_: *mut crate::leanh::LeanObject,
    mut v_hhi_635_: *mut crate::leanh::LeanObject,
    mut v_pivot_636_: *mut crate::leanh::LeanObject,
    mut v_as_637_: *mut crate::leanh::LeanObject,
    mut v_i_638_: *mut crate::leanh::LeanObject,
    mut v_k_639_: *mut crate::leanh::LeanObject,
    mut v_ilo_640_: *mut crate::leanh::LeanObject,
    mut v_ik_641_: *mut crate::leanh::LeanObject,
    mut v_w_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_644_: *mut crate::leanh::LeanObject,
    mut v_n_645_: *mut crate::leanh::LeanObject,
    mut v_lt_646_: *mut crate::leanh::LeanObject,
    mut v_lo_647_: *mut crate::leanh::LeanObject,
    mut v_hi_648_: *mut crate::leanh::LeanObject,
    mut v_hhi_649_: *mut crate::leanh::LeanObject,
    mut v_pivot_650_: *mut crate::leanh::LeanObject,
    mut v_as_651_: *mut crate::leanh::LeanObject,
    mut v_i_652_: *mut crate::leanh::LeanObject,
    mut v_k_653_: *mut crate::leanh::LeanObject,
    mut v_ilo_654_: *mut crate::leanh::LeanObject,
    mut v_ik_655_: *mut crate::leanh::LeanObject,
    mut v_w_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_hi_648_);
    crate::leanh::lean_dec(v_lo_647_);
    crate::leanh::lean_dec(v_n_645_);
    return v_res_657_;
}
pub unsafe fn l_Array_qpartition___redArg(
    mut v_as_658_: *mut crate::leanh::LeanObject,
    mut v_lt_659_: *mut crate::leanh::LeanObject,
    mut v_lo_660_: *mut crate::leanh::LeanObject,
    mut v_hi_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_666_ = lean_nat_add(v_lo_660_, v_hi_661_);
                v___x_667_ = crate::leanh::lean_unsigned_to_nat(1);
                v_mid_668_ = lean_nat_shiftr(v___x_666_, v___x_667_);
                crate::leanh::lean_dec(v___x_666_);
                v___x_683_ = lean_array_fget_borrowed(v_as_658_, v_mid_668_);
                v___x_684_ = lean_array_fget_borrowed(v_as_658_, v_lo_660_);
                crate::leanh::lean_inc_ref(v_lt_659_);
                crate::leanh::lean_inc(v___x_684_);
                crate::leanh::lean_inc(v___x_683_);
                v___x_685_ = crate::leanh::lean_apply_2(v_lt_659_, v___x_683_, v___x_684_);
                v___x_686_ = (crate::leanh::lean_unbox(v___x_685_) as u8);
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
                crate::leanh::lean_inc(v_lo_660_);
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
                crate::leanh::lean_inc_ref(v_lt_659_);
                crate::leanh::lean_inc(v___x_672_);
                crate::leanh::lean_inc(v___x_671_);
                v___x_673_ = crate::leanh::lean_apply_2(v_lt_659_, v___x_671_, v___x_672_);
                v___x_674_ = (crate::leanh::lean_unbox(v___x_673_) as u8);
                if v___x_674_ == 0 {
                    crate::leanh::lean_dec(v_mid_668_);
                    v___y_663_ = v___y_670_;
                    state = 1;
                    continue;
                } else {
                    v___x_675_ = lean_array_fswap(v___y_670_, v_mid_668_, v_hi_661_);
                    crate::leanh::lean_dec(v_mid_668_);
                    v___y_663_ = v___x_675_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_678_ = lean_array_fget_borrowed(v___y_677_, v_hi_661_);
                v___x_679_ = lean_array_fget_borrowed(v___y_677_, v_lo_660_);
                crate::leanh::lean_inc_ref(v_lt_659_);
                crate::leanh::lean_inc(v___x_679_);
                crate::leanh::lean_inc(v___x_678_);
                v___x_680_ = crate::leanh::lean_apply_2(v_lt_659_, v___x_678_, v___x_679_);
                v___x_681_ = (crate::leanh::lean_unbox(v___x_680_) as u8);
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
    mut v_as_688_: *mut crate::leanh::LeanObject,
    mut v_lt_689_: *mut crate::leanh::LeanObject,
    mut v_lo_690_: *mut crate::leanh::LeanObject,
    mut v_hi_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Array_qpartition___redArg(v_as_688_, v_lt_689_, v_lo_690_, v_hi_691_);
    crate::leanh::lean_dec(v_hi_691_);
    return v_res_692_;
}
pub unsafe fn l_Array_qpartition(
    mut v_00_u03b1_693_: *mut crate::leanh::LeanObject,
    mut v_n_694_: *mut crate::leanh::LeanObject,
    mut v_as_695_: *mut crate::leanh::LeanObject,
    mut v_lt_696_: *mut crate::leanh::LeanObject,
    mut v_lo_697_: *mut crate::leanh::LeanObject,
    mut v_hi_698_: *mut crate::leanh::LeanObject,
    mut v_w_699_: *mut crate::leanh::LeanObject,
    mut v_hlo_700_: *mut crate::leanh::LeanObject,
    mut v_hhi_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: u8 = 0;
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_706_ = lean_nat_add(v_lo_697_, v_hi_698_);
                v___x_707_ = crate::leanh::lean_unsigned_to_nat(1);
                v_mid_708_ = lean_nat_shiftr(v___x_706_, v___x_707_);
                crate::leanh::lean_dec(v___x_706_);
                v___x_723_ = lean_array_fget_borrowed(v_as_695_, v_mid_708_);
                v___x_724_ = lean_array_fget_borrowed(v_as_695_, v_lo_697_);
                crate::leanh::lean_inc_ref(v_lt_696_);
                crate::leanh::lean_inc(v___x_724_);
                crate::leanh::lean_inc(v___x_723_);
                v___x_725_ = crate::leanh::lean_apply_2(v_lt_696_, v___x_723_, v___x_724_);
                v___x_726_ = (crate::leanh::lean_unbox(v___x_725_) as u8);
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
                crate::leanh::lean_inc(v_lo_697_);
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
                crate::leanh::lean_inc_ref(v_lt_696_);
                crate::leanh::lean_inc(v___x_712_);
                crate::leanh::lean_inc(v___x_711_);
                v___x_713_ = crate::leanh::lean_apply_2(v_lt_696_, v___x_711_, v___x_712_);
                v___x_714_ = (crate::leanh::lean_unbox(v___x_713_) as u8);
                if v___x_714_ == 0 {
                    crate::leanh::lean_dec(v_mid_708_);
                    v___y_703_ = v___y_710_;
                    state = 1;
                    continue;
                } else {
                    v___x_715_ = lean_array_fswap(v___y_710_, v_mid_708_, v_hi_698_);
                    crate::leanh::lean_dec(v_mid_708_);
                    v___y_703_ = v___x_715_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_718_ = lean_array_fget_borrowed(v___y_717_, v_hi_698_);
                v___x_719_ = lean_array_fget_borrowed(v___y_717_, v_lo_697_);
                crate::leanh::lean_inc_ref(v_lt_696_);
                crate::leanh::lean_inc(v___x_719_);
                crate::leanh::lean_inc(v___x_718_);
                v___x_720_ = crate::leanh::lean_apply_2(v_lt_696_, v___x_718_, v___x_719_);
                v___x_721_ = (crate::leanh::lean_unbox(v___x_720_) as u8);
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
    mut v_00_u03b1_728_: *mut crate::leanh::LeanObject,
    mut v_n_729_: *mut crate::leanh::LeanObject,
    mut v_as_730_: *mut crate::leanh::LeanObject,
    mut v_lt_731_: *mut crate::leanh::LeanObject,
    mut v_lo_732_: *mut crate::leanh::LeanObject,
    mut v_hi_733_: *mut crate::leanh::LeanObject,
    mut v_w_734_: *mut crate::leanh::LeanObject,
    mut v_hlo_735_: *mut crate::leanh::LeanObject,
    mut v_hhi_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_hi_733_);
    crate::leanh::lean_dec(v_n_729_);
    return v_res_737_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Array_qsort___auto__1___closed__0;
    v___x_745_ = l_Lean_mkAtom(v___x_744_);
    return v___x_745_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__2),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__2_once),
        _init_l_Array_qsort___auto__1___closed__2,
    );
    v___x_747_ = l_Array_qpartition___auto__1___closed__5;
    v___x_748_ = lean_array_push(v___x_747_, v___x_746_);
    return v___x_748_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_763_ = l_Array_qsort___auto__1___closed__9;
    v___x_764_ = l_Lean_mkAtom(v___x_763_);
    return v___x_764_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__10_once),
        _init_l_Array_qsort___auto__1___closed__10,
    );
    v___x_766_ = l_Array_qpartition___auto__1___closed__5;
    v___x_767_ = lean_array_push(v___x_766_, v___x_765_);
    return v___x_767_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Array_qsort___auto__1___closed__14;
    v___x_773_ = lean_string_utf8_byte_size(v___x_772_);
    return v___x_773_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__15_once),
        _init_l_Array_qsort___auto__1___closed__15,
    );
    v___x_775_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_776_ = l_Array_qsort___auto__1___closed__14;
    v___x_777_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_777_, 0, v___x_776_);
    crate::leanh::lean_ctor_set(v___x_777_, 1, v___x_775_);
    crate::leanh::lean_ctor_set(v___x_777_, 2, v___x_774_);
    return v___x_777_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_778_ = crate::leanh::lean_box(0);
    v___x_779_ = crate::leanh::lean_box(0);
    v___x_780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__16_once),
        _init_l_Array_qsort___auto__1___closed__16,
    );
    v___x_781_ = crate::leanh::lean_box(2);
    v___x_782_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_782_, 0, v___x_781_);
    crate::leanh::lean_ctor_set(v___x_782_, 1, v___x_780_);
    crate::leanh::lean_ctor_set(v___x_782_, 2, v___x_779_);
    crate::leanh::lean_ctor_set(v___x_782_, 3, v___x_778_);
    return v___x_782_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__17_once),
        _init_l_Array_qsort___auto__1___closed__17,
    );
    v___x_784_ = l_Array_qpartition___auto__1___closed__5;
    v___x_785_ = lean_array_push(v___x_784_, v___x_783_);
    return v___x_785_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_786_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__18_once),
        _init_l_Array_qsort___auto__1___closed__18,
    );
    v___x_787_ = l_Array_qsort___auto__1___closed__13;
    v___x_788_ = crate::leanh::lean_box(2);
    v___x_789_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_789_, 0, v___x_788_);
    crate::leanh::lean_ctor_set(v___x_789_, 1, v___x_787_);
    crate::leanh::lean_ctor_set(v___x_789_, 2, v___x_786_);
    return v___x_789_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19_once),
        _init_l_Array_qsort___auto__1___closed__19,
    );
    v___x_791_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__11_once),
        _init_l_Array_qsort___auto__1___closed__11,
    );
    v___x_792_ = lean_array_push(v___x_791_, v___x_790_);
    return v___x_792_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__20_once),
        _init_l_Array_qsort___auto__1___closed__20,
    );
    v___x_794_ = l_Array_qsort___auto__1___closed__8;
    v___x_795_ = crate::leanh::lean_box(2);
    v___x_796_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_796_, 0, v___x_795_);
    crate::leanh::lean_ctor_set(v___x_796_, 1, v___x_794_);
    crate::leanh::lean_ctor_set(v___x_796_, 2, v___x_793_);
    return v___x_796_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__21_once),
        _init_l_Array_qsort___auto__1___closed__21,
    );
    v___x_798_ = l_Array_qpartition___auto__1___closed__5;
    v___x_799_ = lean_array_push(v___x_798_, v___x_797_);
    return v___x_799_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Array_qsort___auto__1___closed__27;
    v___x_811_ = l_Lean_mkAtom(v___x_810_);
    return v___x_811_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__28_once),
        _init_l_Array_qsort___auto__1___closed__28,
    );
    v___x_813_ = l_Array_qpartition___auto__1___closed__5;
    v___x_814_ = lean_array_push(v___x_813_, v___x_812_);
    return v___x_814_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__30() -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19_once),
        _init_l_Array_qsort___auto__1___closed__19,
    );
    v___x_816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__29_once),
        _init_l_Array_qsort___auto__1___closed__29,
    );
    v___x_817_ = lean_array_push(v___x_816_, v___x_815_);
    return v___x_817_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__31() -> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__30_once),
        _init_l_Array_qsort___auto__1___closed__30,
    );
    v___x_819_ = l_Array_qsort___auto__1___closed__26;
    v___x_820_ = crate::leanh::lean_box(2);
    v___x_821_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_821_, 0, v___x_820_);
    crate::leanh::lean_ctor_set(v___x_821_, 1, v___x_819_);
    crate::leanh::lean_ctor_set(v___x_821_, 2, v___x_818_);
    return v___x_821_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_822_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31_once),
        _init_l_Array_qsort___auto__1___closed__31,
    );
    v___x_823_ = l_Array_qpartition___auto__1___closed__5;
    v___x_824_ = lean_array_push(v___x_823_, v___x_822_);
    return v___x_824_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__34() -> *mut crate::leanh::LeanObject {
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = l_Array_qsort___auto__1___closed__33;
    v___x_827_ = l_Lean_mkAtom(v___x_826_);
    return v___x_827_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__35() -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__34_once),
        _init_l_Array_qsort___auto__1___closed__34,
    );
    v___x_829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__32_once),
        _init_l_Array_qsort___auto__1___closed__32,
    );
    v___x_830_ = lean_array_push(v___x_829_, v___x_828_);
    return v___x_830_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__36() -> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31_once),
        _init_l_Array_qsort___auto__1___closed__31,
    );
    v___x_832_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__35),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__35_once),
        _init_l_Array_qsort___auto__1___closed__35,
    );
    v___x_833_ = lean_array_push(v___x_832_, v___x_831_);
    return v___x_833_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__37() -> *mut crate::leanh::LeanObject {
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__36_once),
        _init_l_Array_qsort___auto__1___closed__36,
    );
    v___x_835_ = l_Array_qsort___auto__1___closed__24;
    v___x_836_ = crate::leanh::lean_box(2);
    v___x_837_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_837_, 0, v___x_836_);
    crate::leanh::lean_ctor_set(v___x_837_, 1, v___x_835_);
    crate::leanh::lean_ctor_set(v___x_837_, 2, v___x_834_);
    return v___x_837_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__38() -> *mut crate::leanh::LeanObject {
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__37),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__37_once),
        _init_l_Array_qsort___auto__1___closed__37,
    );
    v___x_839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__22_once),
        _init_l_Array_qsort___auto__1___closed__22,
    );
    v___x_840_ = lean_array_push(v___x_839_, v___x_838_);
    return v___x_840_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__40() -> *mut crate::leanh::LeanObject {
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_842_ = l_Array_qsort___auto__1___closed__39;
    v___x_843_ = l_Lean_mkAtom(v___x_842_);
    return v___x_843_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__41() -> *mut crate::leanh::LeanObject {
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__40_once),
        _init_l_Array_qsort___auto__1___closed__40,
    );
    v___x_845_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__38_once),
        _init_l_Array_qsort___auto__1___closed__38,
    );
    v___x_846_ = lean_array_push(v___x_845_, v___x_844_);
    return v___x_846_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__42() -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__41_once),
        _init_l_Array_qsort___auto__1___closed__41,
    );
    v___x_848_ = l_Array_qsort___auto__1___closed__6;
    v___x_849_ = crate::leanh::lean_box(2);
    v___x_850_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_850_, 0, v___x_849_);
    crate::leanh::lean_ctor_set(v___x_850_, 1, v___x_848_);
    crate::leanh::lean_ctor_set(v___x_850_, 2, v___x_847_);
    return v___x_850_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__43() -> *mut crate::leanh::LeanObject {
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__42_once),
        _init_l_Array_qsort___auto__1___closed__42,
    );
    v___x_852_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__3),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__3_once),
        _init_l_Array_qsort___auto__1___closed__3,
    );
    v___x_853_ = lean_array_push(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__44() -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__43_once),
        _init_l_Array_qsort___auto__1___closed__43,
    );
    v___x_855_ = l_Array_qsort___auto__1___closed__1;
    v___x_856_ = crate::leanh::lean_box(2);
    v___x_857_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_857_, 0, v___x_856_);
    crate::leanh::lean_ctor_set(v___x_857_, 1, v___x_855_);
    crate::leanh::lean_ctor_set(v___x_857_, 2, v___x_854_);
    return v___x_857_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__45() -> *mut crate::leanh::LeanObject {
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__44_once),
        _init_l_Array_qsort___auto__1___closed__44,
    );
    v___x_859_ = l_Array_qpartition___auto__1___closed__5;
    v___x_860_ = lean_array_push(v___x_859_, v___x_858_);
    return v___x_860_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__46() -> *mut crate::leanh::LeanObject {
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__45_once),
        _init_l_Array_qsort___auto__1___closed__45,
    );
    v___x_862_ = l_Array_qpartition___auto__1___closed__9;
    v___x_863_ = crate::leanh::lean_box(2);
    v___x_864_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_864_, 0, v___x_863_);
    crate::leanh::lean_ctor_set(v___x_864_, 1, v___x_862_);
    crate::leanh::lean_ctor_set(v___x_864_, 2, v___x_861_);
    return v___x_864_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__47() -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__46_once),
        _init_l_Array_qsort___auto__1___closed__46,
    );
    v___x_866_ = l_Array_qpartition___auto__1___closed__5;
    v___x_867_ = lean_array_push(v___x_866_, v___x_865_);
    return v___x_867_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__48() -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__47_once),
        _init_l_Array_qsort___auto__1___closed__47,
    );
    v___x_869_ = l_Array_qpartition___auto__1___closed__7;
    v___x_870_ = crate::leanh::lean_box(2);
    v___x_871_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_871_, 0, v___x_870_);
    crate::leanh::lean_ctor_set(v___x_871_, 1, v___x_869_);
    crate::leanh::lean_ctor_set(v___x_871_, 2, v___x_868_);
    return v___x_871_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__49() -> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__48_once),
        _init_l_Array_qsort___auto__1___closed__48,
    );
    v___x_873_ = l_Array_qpartition___auto__1___closed__5;
    v___x_874_ = lean_array_push(v___x_873_, v___x_872_);
    return v___x_874_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__50() -> *mut crate::leanh::LeanObject {
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__49),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__49_once),
        _init_l_Array_qsort___auto__1___closed__49,
    );
    v___x_876_ = l_Array_qpartition___auto__1___closed__4;
    v___x_877_ = crate::leanh::lean_box(2);
    v___x_878_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_878_, 0, v___x_877_);
    crate::leanh::lean_ctor_set(v___x_878_, 1, v___x_876_);
    crate::leanh::lean_ctor_set(v___x_878_, 2, v___x_875_);
    return v___x_878_;
}
pub unsafe fn _init_l_Array_qsort___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__50_once),
        _init_l_Array_qsort___auto__1___closed__50,
    );
    return v___x_879_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_880_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_881_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_882_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
    mut v_lt_883_: *mut crate::leanh::LeanObject,
    mut v_as_884_: *mut crate::leanh::LeanObject,
    mut v_lo_885_: *mut crate::leanh::LeanObject,
    mut v_hi_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: u8 = 0;
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_898_ = lean_nat_dec_lt(v_lo_885_, v_hi_886_);
                if v___x_898_ == 0 {
                    crate::leanh::lean_dec(v_lo_885_);
                    crate::leanh::lean_dec_ref(v_lt_883_);
                    return v_as_884_;
                } else {
                    v___x_899_ = lean_nat_add(v_lo_885_, v_hi_886_);
                    v___x_900_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_901_ = lean_nat_shiftr(v___x_899_, v___x_900_);
                    crate::leanh::lean_dec(v___x_899_);
                    v___x_916_ = lean_array_fget_borrowed(v_as_884_, v_mid_901_);
                    v___x_917_ = lean_array_fget_borrowed(v_as_884_, v_lo_885_);
                    crate::leanh::lean_inc_ref(v_lt_883_);
                    crate::leanh::lean_inc(v___x_917_);
                    crate::leanh::lean_inc(v___x_916_);
                    v___x_918_ = crate::leanh::lean_apply_2(v_lt_883_, v___x_916_, v___x_917_);
                    v___x_919_ = (crate::leanh::lean_unbox(v___x_918_) as u8);
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
                crate::leanh::lean_inc_n(v_lo_885_, 2);
                crate::leanh::lean_inc_ref(v_lt_883_);
                v___x_890_ =
                    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
                        v_lt_883_,
                        v_hi_886_,
                        v_pivot_889_,
                        v___y_888_,
                        v_lo_885_,
                        v_lo_885_,
                    );
                v_fst_891_ = crate::leanh::lean_ctor_get(v___x_890_, 0);
                crate::leanh::lean_inc(v_fst_891_);
                v_snd_892_ = crate::leanh::lean_ctor_get(v___x_890_, 1);
                crate::leanh::lean_inc(v_snd_892_);
                crate::leanh::lean_dec_ref(v___x_890_);
                v___x_893_ = lean_nat_dec_le(v_hi_886_, v_fst_891_);
                if v___x_893_ == 0 {
                    crate::leanh::lean_inc_ref(v_lt_883_);
                    v___x_894_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_883_, v_snd_892_, v_lo_885_, v_fst_891_,
                        );
                    v___x_895_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_896_ = lean_nat_add(v_fst_891_, v___x_895_);
                    crate::leanh::lean_dec(v_fst_891_);
                    v_as_884_ = v___x_894_;
                    v_lo_885_ = v___x_896_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_891_);
                    crate::leanh::lean_dec(v_lo_885_);
                    crate::leanh::lean_dec_ref(v_lt_883_);
                    return v_snd_892_;
                }
            }
            2 => {
                v___x_904_ = lean_array_fget_borrowed(v___y_903_, v_mid_901_);
                v___x_905_ = lean_array_fget_borrowed(v___y_903_, v_hi_886_);
                crate::leanh::lean_inc_ref(v_lt_883_);
                crate::leanh::lean_inc(v___x_905_);
                crate::leanh::lean_inc(v___x_904_);
                v___x_906_ = crate::leanh::lean_apply_2(v_lt_883_, v___x_904_, v___x_905_);
                v___x_907_ = (crate::leanh::lean_unbox(v___x_906_) as u8);
                if v___x_907_ == 0 {
                    crate::leanh::lean_dec(v_mid_901_);
                    v___y_888_ = v___y_903_;
                    state = 1;
                    continue;
                } else {
                    v___x_908_ = lean_array_fswap(v___y_903_, v_mid_901_, v_hi_886_);
                    crate::leanh::lean_dec(v_mid_901_);
                    v___y_888_ = v___x_908_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_911_ = lean_array_fget_borrowed(v___y_910_, v_hi_886_);
                v___x_912_ = lean_array_fget_borrowed(v___y_910_, v_lo_885_);
                crate::leanh::lean_inc_ref(v_lt_883_);
                crate::leanh::lean_inc(v___x_912_);
                crate::leanh::lean_inc(v___x_911_);
                v___x_913_ = crate::leanh::lean_apply_2(v_lt_883_, v___x_911_, v___x_912_);
                v___x_914_ = (crate::leanh::lean_unbox(v___x_913_) as u8);
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
    mut v_lt_921_: *mut crate::leanh::LeanObject,
    mut v_as_922_: *mut crate::leanh::LeanObject,
    mut v_lo_923_: *mut crate::leanh::LeanObject,
    mut v_hi_924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
        v_lt_921_, v_as_922_, v_lo_923_, v_hi_924_,
    );
    crate::leanh::lean_dec(v_hi_924_);
    return v_res_925_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
    mut v_00_u03b1_926_: *mut crate::leanh::LeanObject,
    mut v_lt_927_: *mut crate::leanh::LeanObject,
    mut v_n_928_: *mut crate::leanh::LeanObject,
    mut v_as_929_: *mut crate::leanh::LeanObject,
    mut v_lo_930_: *mut crate::leanh::LeanObject,
    mut v_hi_931_: *mut crate::leanh::LeanObject,
    mut v_w_932_: *mut crate::leanh::LeanObject,
    mut v_hlo_933_: *mut crate::leanh::LeanObject,
    mut v_hhi_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
        v_lt_927_, v_as_929_, v_lo_930_, v_hi_931_,
    );
    return v___x_935_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___boxed(
    mut v_00_u03b1_936_: *mut crate::leanh::LeanObject,
    mut v_lt_937_: *mut crate::leanh::LeanObject,
    mut v_n_938_: *mut crate::leanh::LeanObject,
    mut v_as_939_: *mut crate::leanh::LeanObject,
    mut v_lo_940_: *mut crate::leanh::LeanObject,
    mut v_hi_941_: *mut crate::leanh::LeanObject,
    mut v_w_942_: *mut crate::leanh::LeanObject,
    mut v_hlo_943_: *mut crate::leanh::LeanObject,
    mut v_hhi_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_hi_941_);
    crate::leanh::lean_dec(v_n_938_);
    return v_res_945_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___redArg(
    mut v_x_946_: *mut crate::leanh::LeanObject,
    mut v_h__1_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_948_ = crate::leanh::lean_ctor_get(v_x_946_, 0);
    crate::leanh::lean_inc(v_fst_948_);
    v_snd_949_ = crate::leanh::lean_ctor_get(v_x_946_, 1);
    crate::leanh::lean_inc(v_snd_949_);
    crate::leanh::lean_dec_ref(v_x_946_);
    v___x_950_ = crate::leanh::lean_apply_3(
        v_h__1_947_,
        v_fst_948_,
        crate::leanh::lean_box(0),
        v_snd_949_,
    );
    return v___x_950_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(
    mut v_00_u03b1_951_: *mut crate::leanh::LeanObject,
    mut v_n_952_: *mut crate::leanh::LeanObject,
    mut v_lo_953_: *mut crate::leanh::LeanObject,
    mut v_hi_954_: *mut crate::leanh::LeanObject,
    mut v_motive_955_: *mut crate::leanh::LeanObject,
    mut v_x_956_: *mut crate::leanh::LeanObject,
    mut v_h__1_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_958_ = crate::leanh::lean_ctor_get(v_x_956_, 0);
    crate::leanh::lean_inc(v_fst_958_);
    v_snd_959_ = crate::leanh::lean_ctor_get(v_x_956_, 1);
    crate::leanh::lean_inc(v_snd_959_);
    crate::leanh::lean_dec_ref(v_x_956_);
    v___x_960_ = crate::leanh::lean_apply_3(
        v_h__1_957_,
        v_fst_958_,
        crate::leanh::lean_box(0),
        v_snd_959_,
    );
    return v___x_960_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___boxed(
    mut v_00_u03b1_961_: *mut crate::leanh::LeanObject,
    mut v_n_962_: *mut crate::leanh::LeanObject,
    mut v_lo_963_: *mut crate::leanh::LeanObject,
    mut v_hi_964_: *mut crate::leanh::LeanObject,
    mut v_motive_965_: *mut crate::leanh::LeanObject,
    mut v_x_966_: *mut crate::leanh::LeanObject,
    mut v_h__1_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(
        v_00_u03b1_961_,
        v_n_962_,
        v_lo_963_,
        v_hi_964_,
        v_motive_965_,
        v_x_966_,
        v_h__1_967_,
    );
    crate::leanh::lean_dec(v_hi_964_);
    crate::leanh::lean_dec(v_lo_963_);
    crate::leanh::lean_dec(v_n_962_);
    return v_res_968_;
}
pub unsafe fn l_Array_qsort___redArg(
    mut v_as_969_: *mut crate::leanh::LeanObject,
    mut v_lt_970_: *mut crate::leanh::LeanObject,
    mut v_lo_971_: *mut crate::leanh::LeanObject,
    mut v_hi_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u8 = 0;
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_979_ = lean_array_get_size(v_as_969_);
                v___x_980_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_981_ = lean_nat_dec_eq(v___x_979_, v___x_980_);
                if v___x_981_ == 0 {
                    v___x_982_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_983_ = lean_nat_sub(v___x_979_, v___x_982_);
                    v___x_987_ = lean_nat_dec_le(v_lo_971_, v___x_983_);
                    if v___x_987_ == 0 {
                        crate::leanh::lean_dec(v_lo_971_);
                        crate::leanh::lean_inc(v___x_983_);
                        v___y_985_ = v___x_983_;
                        state = 2;
                        continue;
                    } else {
                        v___y_985_ = v_lo_971_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_hi_972_);
                    crate::leanh::lean_dec(v_lo_971_);
                    crate::leanh::lean_dec_ref(v_lt_970_);
                    return v_as_969_;
                }
            }
            1 => {
                v___x_976_ = lean_nat_dec_le(v___y_974_, v___y_975_);
                if v___x_976_ == 0 {
                    crate::leanh::lean_dec(v___y_975_);
                    crate::leanh::lean_inc(v___y_974_);
                    v___x_977_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_970_, v_as_969_, v___y_974_, v___y_974_,
                        );
                    crate::leanh::lean_dec(v___y_974_);
                    return v___x_977_;
                } else {
                    v___x_978_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_970_, v_as_969_, v___y_974_, v___y_975_,
                        );
                    crate::leanh::lean_dec(v___y_975_);
                    return v___x_978_;
                }
            }
            2 => {
                v___x_986_ = lean_nat_dec_le(v_hi_972_, v___x_983_);
                if v___x_986_ == 0 {
                    crate::leanh::lean_dec(v_hi_972_);
                    v___y_974_ = v___y_985_;
                    v___y_975_ = v___x_983_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_983_);
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
    mut v_00_u03b1_988_: *mut crate::leanh::LeanObject,
    mut v_as_989_: *mut crate::leanh::LeanObject,
    mut v_lt_990_: *mut crate::leanh::LeanObject,
    mut v_lo_991_: *mut crate::leanh::LeanObject,
    mut v_hi_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: u8 = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_999_ = lean_array_get_size(v_as_989_);
                v___x_1000_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1001_ = lean_nat_dec_eq(v___x_999_, v___x_1000_);
                if v___x_1001_ == 0 {
                    v___x_1002_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1003_ = lean_nat_sub(v___x_999_, v___x_1002_);
                    v___x_1007_ = lean_nat_dec_le(v_lo_991_, v___x_1003_);
                    if v___x_1007_ == 0 {
                        crate::leanh::lean_dec(v_lo_991_);
                        crate::leanh::lean_inc(v___x_1003_);
                        v___y_1005_ = v___x_1003_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1005_ = v_lo_991_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_hi_992_);
                    crate::leanh::lean_dec(v_lo_991_);
                    crate::leanh::lean_dec_ref(v_lt_990_);
                    return v_as_989_;
                }
            }
            1 => {
                v___x_996_ = lean_nat_dec_le(v___y_994_, v___y_995_);
                if v___x_996_ == 0 {
                    crate::leanh::lean_dec(v___y_995_);
                    crate::leanh::lean_inc(v___y_994_);
                    v___x_997_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_990_, v_as_989_, v___y_994_, v___y_994_,
                        );
                    crate::leanh::lean_dec(v___y_994_);
                    return v___x_997_;
                } else {
                    v___x_998_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_990_, v_as_989_, v___y_994_, v___y_995_,
                        );
                    crate::leanh::lean_dec(v___y_995_);
                    return v___x_998_;
                }
            }
            2 => {
                v___x_1006_ = lean_nat_dec_le(v_hi_992_, v___x_1003_);
                if v___x_1006_ == 0 {
                    crate::leanh::lean_dec(v_hi_992_);
                    v___y_994_ = v___y_1005_;
                    v___y_995_ = v___x_1003_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1003_);
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
    mut v_ord_1008_: *mut crate::leanh::LeanObject,
    mut v___x_1009_: u8,
    mut v_x_1010_: *mut crate::leanh::LeanObject,
    mut v_y_1011_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u8 = 0;
    v___x_1012_ = crate::leanh::lean_apply_2(v_ord_1008_, v_x_1010_, v_y_1011_);
    v___x_1013_ = (crate::leanh::lean_unbox(v___x_1012_) as u8);
    if v___x_1013_ == 0 {
        let mut v___x_1014_: u8 = 0;
        v___x_1014_ = 1;
        return v___x_1014_;
    } else {
        return v___x_1009_;
    }
}
pub unsafe fn l_Array_qsortOrd___redArg___lam__0___boxed(
    mut v_ord_1015_: *mut crate::leanh::LeanObject,
    mut v___x_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
    mut v_y_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_63__boxed_1019_: u8 = 0;
    let mut v_res_1020_: u8 = 0;
    let mut v_r_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_63__boxed_1019_ = (crate::leanh::lean_unbox(v___x_1016_) as u8);
    v_res_1020_ = l_Array_qsortOrd___redArg___lam__0(
        v_ord_1015_,
        v___x_63__boxed_1019_,
        v_x_1017_,
        v_y_1018_,
    );
    v_r_1021_ = crate::leanh::lean_box((v_res_1020_) as usize);
    return v_r_1021_;
}
pub unsafe fn l_Array_qsortOrd___redArg(
    mut v_ord_1022_: *mut crate::leanh::LeanObject,
    mut v_xs_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1024_ = lean_array_get_size(v_xs_1023_);
                v___x_1025_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1026_ = lean_nat_dec_eq(v___x_1024_, v___x_1025_);
                if v___x_1026_ == 0 {
                    v___x_1027_ = crate::leanh::lean_box((v___x_1026_) as usize);
                    v___f_1028_ = crate::leanh::lean_alloc_closure(
                        l_Array_qsortOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1028_, 0, v_ord_1022_);
                    crate::leanh::lean_closure_set(v___f_1028_, 1, v___x_1027_);
                    v___x_1029_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1030_ = lean_nat_sub(v___x_1024_, v___x_1029_);
                    v___x_1036_ = lean_nat_dec_le(v___x_1025_, v___x_1030_);
                    if v___x_1036_ == 0 {
                        crate::leanh::lean_inc(v___x_1030_);
                        v___y_1032_ = v___x_1030_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1032_ = v___x_1025_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ord_1022_);
                    return v_xs_1023_;
                }
            }
            1 => {
                v___x_1033_ = lean_nat_dec_le(v___y_1032_, v___x_1030_);
                if v___x_1033_ == 0 {
                    crate::leanh::lean_dec(v___x_1030_);
                    crate::leanh::lean_inc(v___y_1032_);
                    v___x_1034_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v___f_1028_,
                            v_xs_1023_,
                            v___y_1032_,
                            v___y_1032_,
                        );
                    crate::leanh::lean_dec(v___y_1032_);
                    return v___x_1034_;
                } else {
                    v___x_1035_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v___f_1028_,
                            v_xs_1023_,
                            v___y_1032_,
                            v___x_1030_,
                        );
                    crate::leanh::lean_dec(v___x_1030_);
                    return v___x_1035_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qsortOrd(
    mut v_00_u03b1_1037_: *mut crate::leanh::LeanObject,
    mut v_ord_1038_: *mut crate::leanh::LeanObject,
    mut v_xs_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_Array_qsortOrd___redArg(v_ord_1038_, v_xs_1039_);
    return v___x_1040_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_QSort_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Array_QSort_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_qpartition___auto__1 = _init_l_Array_qpartition___auto__1();
    crate::leanh::lean_mark_persistent(l_Array_qpartition___auto__1);
    l_Array_qpartition___auto__3 = _init_l_Array_qpartition___auto__3();
    crate::leanh::lean_mark_persistent(l_Array_qpartition___auto__3);
    l_Array_qpartition___auto__5 = _init_l_Array_qpartition___auto__5();
    crate::leanh::lean_mark_persistent(l_Array_qpartition___auto__5);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6,
    );
    l_Array_qsort___auto__1 = _init_l_Array_qsort___auto__1();
    crate::leanh::lean_mark_persistent(l_Array_qsort___auto__1);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4,
    );
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_QSort_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_QSort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_QSort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_QSort_Basic(builtin);
}
