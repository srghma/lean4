// Lean compiler output
// Module: Init.Data.Array.Lex.Basic
// Imports: Init.Data.Range.Polymorphic.RangeIterator Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Nat Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_utf8_byte_size,
};
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
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub static l_Array_lex___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Array_lex___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Array_lex___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Array_lex___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Array_lex___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Array_lex___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_Array_lex___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Array_lex___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Array_lex___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_Array_lex___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__14_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__15_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Array_lex___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__15_value) as *mut crate::leanh::LeanObject;
static l_Array_lex___auto__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__15_value)
                as *mut crate::leanh::LeanObject,
            7932075773091973500 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__17_value: crate::leanh::LeanStringObject<15> =
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
static mut l_Array_lex___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l_Array_lex___auto__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__17_value)
                as *mut crate::leanh::LeanObject,
            7306243862518720553 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__19_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Array_lex___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__22_value: crate::leanh::LeanStringObject<12> =
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
static mut l_Array_lex___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__22_value)
                as *mut crate::leanh::LeanObject,
            9871775667037945883 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__24_value: crate::leanh::LeanStringObject<12> =
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
static mut l_Array_lex___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__33_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Array_lex___auto__1___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__34_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__33_value)
                as *mut crate::leanh::LeanObject,
            6883052497475924672 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__35_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__35_value) as *mut crate::leanh::LeanObject;
static l_Array_lex___auto__1___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__36_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__35_value)
                as *mut crate::leanh::LeanObject,
            6167508377434939095 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__37_value: crate::leanh::LeanStringObject<3> =
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
static mut l_Array_lex___auto__1___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__37_value) as *mut crate::leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__42_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__43_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Array_lex___auto__1___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__43_value) as *mut crate::leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__46_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__47_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__48_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__49_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Array_lex___auto__1___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__49_value) as *mut crate::leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__50_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__51_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__52_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__53_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__54_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__55_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__56_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__57_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__58_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__59_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__60_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_lex___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_lex___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_lex___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Array_lex___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = l_Array_lex___auto__1___closed__10;
    v___x_267_ = l_Lean_mkAtom(v___x_266_);
    return v___x_267_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__12_once),
        _init_l_Array_lex___auto__1___closed__12,
    );
    v___x_269_ = l_Array_lex___auto__1___closed__5;
    v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
    return v___x_270_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = l_Array_lex___auto__1___closed__19;
    v___x_286_ = l_Lean_mkAtom(v___x_285_);
    return v___x_286_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__20_once),
        _init_l_Array_lex___auto__1___closed__20,
    );
    v___x_288_ = l_Array_lex___auto__1___closed__5;
    v___x_289_ = lean_array_push(v___x_288_, v___x_287_);
    return v___x_289_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = l_Array_lex___auto__1___closed__24;
    v___x_295_ = lean_string_utf8_byte_size(v___x_294_);
    return v___x_295_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_296_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__25_once),
        _init_l_Array_lex___auto__1___closed__25,
    );
    v___x_297_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_298_ = l_Array_lex___auto__1___closed__24;
    v___x_299_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_299_, 0, v___x_298_);
    crate::leanh::lean_ctor_set(v___x_299_, 1, v___x_297_);
    crate::leanh::lean_ctor_set(v___x_299_, 2, v___x_296_);
    return v___x_299_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = crate::leanh::lean_box(0);
    v___x_301_ = crate::leanh::lean_box(0);
    v___x_302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__26_once),
        _init_l_Array_lex___auto__1___closed__26,
    );
    v___x_303_ = crate::leanh::lean_box(2);
    v___x_304_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_304_, 0, v___x_303_);
    crate::leanh::lean_ctor_set(v___x_304_, 1, v___x_302_);
    crate::leanh::lean_ctor_set(v___x_304_, 2, v___x_301_);
    crate::leanh::lean_ctor_set(v___x_304_, 3, v___x_300_);
    return v___x_304_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__27_once),
        _init_l_Array_lex___auto__1___closed__27,
    );
    v___x_306_ = l_Array_lex___auto__1___closed__5;
    v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
    return v___x_307_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__28_once),
        _init_l_Array_lex___auto__1___closed__28,
    );
    v___x_309_ = l_Array_lex___auto__1___closed__23;
    v___x_310_ = crate::leanh::lean_box(2);
    v___x_311_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_311_, 0, v___x_310_);
    crate::leanh::lean_ctor_set(v___x_311_, 1, v___x_309_);
    crate::leanh::lean_ctor_set(v___x_311_, 2, v___x_308_);
    return v___x_311_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__30() -> *mut crate::leanh::LeanObject {
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29_once),
        _init_l_Array_lex___auto__1___closed__29,
    );
    v___x_313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__21_once),
        _init_l_Array_lex___auto__1___closed__21,
    );
    v___x_314_ = lean_array_push(v___x_313_, v___x_312_);
    return v___x_314_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__31() -> *mut crate::leanh::LeanObject {
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__30_once),
        _init_l_Array_lex___auto__1___closed__30,
    );
    v___x_316_ = l_Array_lex___auto__1___closed__18;
    v___x_317_ = crate::leanh::lean_box(2);
    v___x_318_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
    crate::leanh::lean_ctor_set(v___x_318_, 1, v___x_316_);
    crate::leanh::lean_ctor_set(v___x_318_, 2, v___x_315_);
    return v___x_318_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__31_once),
        _init_l_Array_lex___auto__1___closed__31,
    );
    v___x_320_ = l_Array_lex___auto__1___closed__5;
    v___x_321_ = lean_array_push(v___x_320_, v___x_319_);
    return v___x_321_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__38() -> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Array_lex___auto__1___closed__37;
    v___x_333_ = l_Lean_mkAtom(v___x_332_);
    return v___x_333_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__39() -> *mut crate::leanh::LeanObject {
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__38_once),
        _init_l_Array_lex___auto__1___closed__38,
    );
    v___x_335_ = l_Array_lex___auto__1___closed__5;
    v___x_336_ = lean_array_push(v___x_335_, v___x_334_);
    return v___x_336_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__40() -> *mut crate::leanh::LeanObject {
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_337_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29_once),
        _init_l_Array_lex___auto__1___closed__29,
    );
    v___x_338_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__39_once),
        _init_l_Array_lex___auto__1___closed__39,
    );
    v___x_339_ = lean_array_push(v___x_338_, v___x_337_);
    return v___x_339_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__41() -> *mut crate::leanh::LeanObject {
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__40_once),
        _init_l_Array_lex___auto__1___closed__40,
    );
    v___x_341_ = l_Array_lex___auto__1___closed__36;
    v___x_342_ = crate::leanh::lean_box(2);
    v___x_343_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_343_, 0, v___x_342_);
    crate::leanh::lean_ctor_set(v___x_343_, 1, v___x_341_);
    crate::leanh::lean_ctor_set(v___x_343_, 2, v___x_340_);
    return v___x_343_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__42() -> *mut crate::leanh::LeanObject {
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41_once),
        _init_l_Array_lex___auto__1___closed__41,
    );
    v___x_345_ = l_Array_lex___auto__1___closed__5;
    v___x_346_ = lean_array_push(v___x_345_, v___x_344_);
    return v___x_346_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__44() -> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = l_Array_lex___auto__1___closed__43;
    v___x_349_ = l_Lean_mkAtom(v___x_348_);
    return v___x_349_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__45() -> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__44_once),
        _init_l_Array_lex___auto__1___closed__44,
    );
    v___x_351_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__42_once),
        _init_l_Array_lex___auto__1___closed__42,
    );
    v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__46() -> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41_once),
        _init_l_Array_lex___auto__1___closed__41,
    );
    v___x_354_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__45_once),
        _init_l_Array_lex___auto__1___closed__45,
    );
    v___x_355_ = lean_array_push(v___x_354_, v___x_353_);
    return v___x_355_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__47() -> *mut crate::leanh::LeanObject {
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__46_once),
        _init_l_Array_lex___auto__1___closed__46,
    );
    v___x_357_ = l_Array_lex___auto__1___closed__34;
    v___x_358_ = crate::leanh::lean_box(2);
    v___x_359_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_359_, 0, v___x_358_);
    crate::leanh::lean_ctor_set(v___x_359_, 1, v___x_357_);
    crate::leanh::lean_ctor_set(v___x_359_, 2, v___x_356_);
    return v___x_359_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__48() -> *mut crate::leanh::LeanObject {
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__47_once),
        _init_l_Array_lex___auto__1___closed__47,
    );
    v___x_361_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__32_once),
        _init_l_Array_lex___auto__1___closed__32,
    );
    v___x_362_ = lean_array_push(v___x_361_, v___x_360_);
    return v___x_362_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__50() -> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Array_lex___auto__1___closed__49;
    v___x_365_ = l_Lean_mkAtom(v___x_364_);
    return v___x_365_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__51() -> *mut crate::leanh::LeanObject {
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__50_once),
        _init_l_Array_lex___auto__1___closed__50,
    );
    v___x_367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__48_once),
        _init_l_Array_lex___auto__1___closed__48,
    );
    v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
    return v___x_368_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__52() -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__51_once),
        _init_l_Array_lex___auto__1___closed__51,
    );
    v___x_370_ = l_Array_lex___auto__1___closed__16;
    v___x_371_ = crate::leanh::lean_box(2);
    v___x_372_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
    crate::leanh::lean_ctor_set(v___x_372_, 1, v___x_370_);
    crate::leanh::lean_ctor_set(v___x_372_, 2, v___x_369_);
    return v___x_372_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__53() -> *mut crate::leanh::LeanObject {
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__52_once),
        _init_l_Array_lex___auto__1___closed__52,
    );
    v___x_374_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__13_once),
        _init_l_Array_lex___auto__1___closed__13,
    );
    v___x_375_ = lean_array_push(v___x_374_, v___x_373_);
    return v___x_375_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__54() -> *mut crate::leanh::LeanObject {
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__53_once),
        _init_l_Array_lex___auto__1___closed__53,
    );
    v___x_377_ = l_Array_lex___auto__1___closed__11;
    v___x_378_ = crate::leanh::lean_box(2);
    v___x_379_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
    crate::leanh::lean_ctor_set(v___x_379_, 1, v___x_377_);
    crate::leanh::lean_ctor_set(v___x_379_, 2, v___x_376_);
    return v___x_379_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__55() -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__54_once),
        _init_l_Array_lex___auto__1___closed__54,
    );
    v___x_381_ = l_Array_lex___auto__1___closed__5;
    v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
    return v___x_382_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__56() -> *mut crate::leanh::LeanObject {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__55_once),
        _init_l_Array_lex___auto__1___closed__55,
    );
    v___x_384_ = l_Array_lex___auto__1___closed__9;
    v___x_385_ = crate::leanh::lean_box(2);
    v___x_386_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_386_, 0, v___x_385_);
    crate::leanh::lean_ctor_set(v___x_386_, 1, v___x_384_);
    crate::leanh::lean_ctor_set(v___x_386_, 2, v___x_383_);
    return v___x_386_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__57() -> *mut crate::leanh::LeanObject {
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__56_once),
        _init_l_Array_lex___auto__1___closed__56,
    );
    v___x_388_ = l_Array_lex___auto__1___closed__5;
    v___x_389_ = lean_array_push(v___x_388_, v___x_387_);
    return v___x_389_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__58() -> *mut crate::leanh::LeanObject {
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__57_once),
        _init_l_Array_lex___auto__1___closed__57,
    );
    v___x_391_ = l_Array_lex___auto__1___closed__7;
    v___x_392_ = crate::leanh::lean_box(2);
    v___x_393_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_393_, 0, v___x_392_);
    crate::leanh::lean_ctor_set(v___x_393_, 1, v___x_391_);
    crate::leanh::lean_ctor_set(v___x_393_, 2, v___x_390_);
    return v___x_393_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__59() -> *mut crate::leanh::LeanObject {
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__58_once),
        _init_l_Array_lex___auto__1___closed__58,
    );
    v___x_395_ = l_Array_lex___auto__1___closed__5;
    v___x_396_ = lean_array_push(v___x_395_, v___x_394_);
    return v___x_396_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__60() -> *mut crate::leanh::LeanObject {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__59),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__59_once),
        _init_l_Array_lex___auto__1___closed__59,
    );
    v___x_398_ = l_Array_lex___auto__1___closed__4;
    v___x_399_ = crate::leanh::lean_box(2);
    v___x_400_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_400_, 0, v___x_399_);
    crate::leanh::lean_ctor_set(v___x_400_, 1, v___x_398_);
    crate::leanh::lean_ctor_set(v___x_400_, 2, v___x_397_);
    return v___x_400_;
}
pub unsafe fn _init_l_Array_lex___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__60),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__60_once),
        _init_l_Array_lex___auto__1___closed__60,
    );
    return v___x_401_;
}
pub unsafe fn l_Array_lex___redArg___lam__0(
    mut v___y_402_: *mut crate::leanh::LeanObject,
    mut v_as_403_: *mut crate::leanh::LeanObject,
    mut v_bs_404_: *mut crate::leanh::LeanObject,
    mut v_lt_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
    mut v___x_407_: *mut crate::leanh::LeanObject,
    mut v___x_408_: *mut crate::leanh::LeanObject,
    mut v_next_409_: *mut crate::leanh::LeanObject,
    mut v_acc_410_: *mut crate::leanh::LeanObject,
    mut v_h_411_: *mut crate::leanh::LeanObject,
    mut v_G_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: u8 = 0;
    v___x_413_ = lean_nat_dec_lt(v_next_409_, v___y_402_);
    if v___x_413_ == 0 {
        crate::leanh::lean_dec_ref(v_G_412_);
        crate::leanh::lean_dec_ref(v___x_408_);
        crate::leanh::lean_dec_ref(v_inst_406_);
        crate::leanh::lean_dec_ref(v_lt_405_);
        crate::leanh::lean_inc_ref(v_acc_410_);
        return v_acc_410_;
    } else {
        let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: u8 = 0;
        v___x_414_ = lean_array_fget_borrowed(v_as_403_, v_next_409_);
        v___x_415_ = lean_array_fget_borrowed(v_bs_404_, v_next_409_);
        crate::leanh::lean_inc(v___x_415_);
        crate::leanh::lean_inc(v___x_414_);
        v___x_416_ = crate::leanh::lean_apply_2(v_lt_405_, v___x_414_, v___x_415_);
        v___x_417_ = (crate::leanh::lean_unbox(v___x_416_) as u8);
        if v___x_417_ == 0 {
            let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_419_: u8 = 0;
            crate::leanh::lean_inc(v___x_415_);
            crate::leanh::lean_inc(v___x_414_);
            v___x_418_ = crate::leanh::lean_apply_2(v_inst_406_, v___x_414_, v___x_415_);
            v___x_419_ = (crate::leanh::lean_unbox(v___x_418_) as u8);
            if v___x_419_ == 0 {
                let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_G_412_);
                crate::leanh::lean_dec_ref(v___x_408_);
                v___x_420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_420_, 0, v___x_416_);
                v___x_421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_421_, 0, v___x_420_);
                crate::leanh::lean_ctor_set(v___x_421_, 1, v___x_407_);
                return v___x_421_;
            } else {
                let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_422_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_423_ = lean_nat_add(v_next_409_, v___x_422_);
                v___x_424_ = crate::leanh::lean_apply_4(
                    v_G_412_,
                    v___x_423_,
                    v___x_408_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_424_;
            }
        } else {
            let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_G_412_);
            crate::leanh::lean_dec_ref(v___x_408_);
            crate::leanh::lean_dec_ref(v_inst_406_);
            v___x_425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_425_, 0, v___x_416_);
            v___x_426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_426_, 0, v___x_425_);
            crate::leanh::lean_ctor_set(v___x_426_, 1, v___x_407_);
            return v___x_426_;
        }
    }
}
pub unsafe fn l_Array_lex___redArg___lam__0___boxed(
    mut v___y_427_: *mut crate::leanh::LeanObject,
    mut v_as_428_: *mut crate::leanh::LeanObject,
    mut v_bs_429_: *mut crate::leanh::LeanObject,
    mut v_lt_430_: *mut crate::leanh::LeanObject,
    mut v_inst_431_: *mut crate::leanh::LeanObject,
    mut v___x_432_: *mut crate::leanh::LeanObject,
    mut v___x_433_: *mut crate::leanh::LeanObject,
    mut v_next_434_: *mut crate::leanh::LeanObject,
    mut v_acc_435_: *mut crate::leanh::LeanObject,
    mut v_h_436_: *mut crate::leanh::LeanObject,
    mut v_G_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_acc_435_);
    crate::leanh::lean_dec(v_next_434_);
    crate::leanh::lean_dec_ref(v_bs_429_);
    crate::leanh::lean_dec_ref(v_as_428_);
    crate::leanh::lean_dec(v___y_427_);
    return v_res_438_;
}
pub unsafe fn l_Array_lex___redArg(
    mut v_inst_442_: *mut crate::leanh::LeanObject,
    mut v_as_443_: *mut crate::leanh::LeanObject,
    mut v_bs_444_: *mut crate::leanh::LeanObject,
    mut v_lt_445_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    let mut v_val_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v___x_459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_446_ = crate::leanh::lean_unsigned_to_nat(0);
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
                v___x_451_ = crate::leanh::lean_box(0);
                v___x_452_ = l_Array_lex___redArg___closed__0;
                v___f_453_ = crate::leanh::lean_alloc_closure(
                    l_Array_lex___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_453_, 0, v___y_450_);
                crate::leanh::lean_closure_set(v___f_453_, 1, v_as_443_);
                crate::leanh::lean_closure_set(v___f_453_, 2, v_bs_444_);
                crate::leanh::lean_closure_set(v___f_453_, 3, v_lt_445_);
                crate::leanh::lean_closure_set(v___f_453_, 4, v_inst_442_);
                crate::leanh::lean_closure_set(v___f_453_, 5, v___x_451_);
                crate::leanh::lean_closure_set(v___f_453_, 6, v___x_452_);
                v___x_454_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_453_,
                    v___x_446_,
                    v___x_452_,
                    crate::leanh::lean_box(0),
                );
                v_fst_455_ = crate::leanh::lean_ctor_get(v___x_454_, 0);
                crate::leanh::lean_inc(v_fst_455_);
                crate::leanh::lean_dec(v___x_454_);
                if crate::leanh::lean_obj_tag(v_fst_455_) == 0 {
                    v___x_456_ = lean_nat_dec_lt(v___x_447_, v___x_448_);
                    return v___x_456_;
                } else {
                    v_val_457_ = crate::leanh::lean_ctor_get(v_fst_455_, 0);
                    crate::leanh::lean_inc(v_val_457_);
                    crate::leanh::lean_dec_ref_known(v_fst_455_, 1);
                    v___x_458_ = (crate::leanh::lean_unbox(v_val_457_) as u8);
                    crate::leanh::lean_dec(v_val_457_);
                    return v___x_458_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_lex___redArg___boxed(
    mut v_inst_460_: *mut crate::leanh::LeanObject,
    mut v_as_461_: *mut crate::leanh::LeanObject,
    mut v_bs_462_: *mut crate::leanh::LeanObject,
    mut v_lt_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_464_: u8 = 0;
    let mut v_r_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Array_lex___redArg(v_inst_460_, v_as_461_, v_bs_462_, v_lt_463_);
    v_r_465_ = crate::leanh::lean_box((v_res_464_) as usize);
    return v_r_465_;
}
pub unsafe fn l_Array_lex(
    mut v_00_u03b1_466_: *mut crate::leanh::LeanObject,
    mut v_inst_467_: *mut crate::leanh::LeanObject,
    mut v_as_468_: *mut crate::leanh::LeanObject,
    mut v_bs_469_: *mut crate::leanh::LeanObject,
    mut v_lt_470_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_471_: u8 = 0;
    v___x_471_ = l_Array_lex___redArg(v_inst_467_, v_as_468_, v_bs_469_, v_lt_470_);
    return v___x_471_;
}
pub unsafe fn l_Array_lex___boxed(
    mut v_00_u03b1_472_: *mut crate::leanh::LeanObject,
    mut v_inst_473_: *mut crate::leanh::LeanObject,
    mut v_as_474_: *mut crate::leanh::LeanObject,
    mut v_bs_475_: *mut crate::leanh::LeanObject,
    mut v_lt_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_477_: u8 = 0;
    let mut v_r_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Array_lex(
        v_00_u03b1_472_,
        v_inst_473_,
        v_as_474_,
        v_bs_475_,
        v_lt_476_,
    );
    v_r_478_ = crate::leanh::lean_box((v_res_477_) as usize);
    return v_r_478_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Lex_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Array_Lex_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_lex___auto__1 = _init_l_Array_lex___auto__1();
    crate::leanh::lean_mark_persistent(l_Array_lex___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Lex_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Lex_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Lex_Basic(builtin);
}
