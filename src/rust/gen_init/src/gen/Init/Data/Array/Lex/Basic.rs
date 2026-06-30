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
pub static l_Array_lex___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Array_lex___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Array_lex___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
static mut l_Array_lex___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__3_value) as *mut leanh::LeanObject;
static l_Array_lex___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
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
static mut l_Array_lex___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__6_value: leanh::LeanStringObject<19> =
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
static mut l_Array_lex___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__6_value) as *mut leanh::LeanObject;
static l_Array_lex___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__10_value: leanh::LeanStringObject<6> =
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
static mut l_Array_lex___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__10_value) as *mut leanh::LeanObject;
static l_Array_lex___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__11_value) as *mut leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__14_value: leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__15_value: leanh::LeanStringObject<6> =
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
static mut l_Array_lex___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__15_value) as *mut leanh::LeanObject;
static l_Array_lex___auto__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__15_value)
                as *mut leanh::LeanObject,
            7932075773091973500 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__17_value: leanh::LeanStringObject<15> =
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
static mut l_Array_lex___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__17_value) as *mut leanh::LeanObject;
static l_Array_lex___auto__1___closed__18_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__18_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__18_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__17_value)
                as *mut leanh::LeanObject,
            7306243862518720553 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__19_value: leanh::LeanStringObject<2> =
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
static mut l_Array_lex___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__19_value) as *mut leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__22_value: leanh::LeanStringObject<12> =
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
static mut l_Array_lex___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__23_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__22_value)
                as *mut leanh::LeanObject,
            9871775667037945883 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__24_value: leanh::LeanStringObject<12> =
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
static mut l_Array_lex___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__24_value) as *mut leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__31_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__33_value: leanh::LeanStringObject<8> =
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
static mut l_Array_lex___auto__1___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__33_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__34_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__33_value)
                as *mut leanh::LeanObject,
            6883052497475924672 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__34_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__35_value: leanh::LeanStringObject<5> =
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
static mut l_Array_lex___auto__1___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__35_value) as *mut leanh::LeanObject;
static l_Array_lex___auto__1___closed__36_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__36_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_lex___auto__1___closed__36_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_lex___auto__1___closed__36_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_lex___auto__1___closed__35_value)
                as *mut leanh::LeanObject,
            6167508377434939095 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___auto__1___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__36_value) as *mut leanh::LeanObject;
pub static l_Array_lex___auto__1___closed__37_value: leanh::LeanStringObject<3> =
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
static mut l_Array_lex___auto__1___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__37_value) as *mut leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__39_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__43_value: leanh::LeanStringObject<2> =
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
static mut l_Array_lex___auto__1___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__43_value) as *mut leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__45: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__46_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__46: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__47_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__47: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__48_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__48: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_lex___auto__1___closed__49_value: leanh::LeanStringObject<2> =
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
static mut l_Array_lex___auto__1___closed__49: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___auto__1___closed__49_value) as *mut leanh::LeanObject;
static mut l_Array_lex___auto__1___closed__50_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__50: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__51_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__51: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__52_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__52: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__53_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__53: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__54_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__54: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__55_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__55: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__56_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__56: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__57_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__57: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__58_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__58: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__59_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__59: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_lex___auto__1___closed__60_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_lex___auto__1___closed__60: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_lex___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_lex___redArg___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_lex___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_lex___redArg___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Array_lex___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = l_Array_lex___auto__1___closed__10;
    v___x_267_ = l_Lean_mkAtom(v___x_266_);
    return v___x_267_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__12_once),
        _init_l_Array_lex___auto__1___closed__12,
    );
    v___x_269_ = l_Array_lex___auto__1___closed__5;
    v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
    return v___x_270_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = l_Array_lex___auto__1___closed__19;
    v___x_286_ = l_Lean_mkAtom(v___x_285_);
    return v___x_286_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__20_once),
        _init_l_Array_lex___auto__1___closed__20,
    );
    v___x_288_ = l_Array_lex___auto__1___closed__5;
    v___x_289_ = lean_array_push(v___x_288_, v___x_287_);
    return v___x_289_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = l_Array_lex___auto__1___closed__24;
    v___x_295_ = lean_string_utf8_byte_size(v___x_294_);
    return v___x_295_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_296_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__25_once),
        _init_l_Array_lex___auto__1___closed__25,
    );
    v___x_297_ = leanh::lean_unsigned_to_nat(0);
    v___x_298_ = l_Array_lex___auto__1___closed__24;
    v___x_299_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_299_, 0, v___x_298_);
    leanh::lean_ctor_set(v___x_299_, 1, v___x_297_);
    leanh::lean_ctor_set(v___x_299_, 2, v___x_296_);
    return v___x_299_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = leanh::lean_box(0);
    v___x_301_ = leanh::lean_box(0);
    v___x_302_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__26_once),
        _init_l_Array_lex___auto__1___closed__26,
    );
    v___x_303_ = leanh::lean_box(2);
    v___x_304_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_304_, 0, v___x_303_);
    leanh::lean_ctor_set(v___x_304_, 1, v___x_302_);
    leanh::lean_ctor_set(v___x_304_, 2, v___x_301_);
    leanh::lean_ctor_set(v___x_304_, 3, v___x_300_);
    return v___x_304_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__27_once),
        _init_l_Array_lex___auto__1___closed__27,
    );
    v___x_306_ = l_Array_lex___auto__1___closed__5;
    v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
    return v___x_307_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__28_once),
        _init_l_Array_lex___auto__1___closed__28,
    );
    v___x_309_ = l_Array_lex___auto__1___closed__23;
    v___x_310_ = leanh::lean_box(2);
    v___x_311_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_311_, 0, v___x_310_);
    leanh::lean_ctor_set(v___x_311_, 1, v___x_309_);
    leanh::lean_ctor_set(v___x_311_, 2, v___x_308_);
    return v___x_311_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__30() -> *mut leanh::LeanObject {
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29_once),
        _init_l_Array_lex___auto__1___closed__29,
    );
    v___x_313_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__21_once),
        _init_l_Array_lex___auto__1___closed__21,
    );
    v___x_314_ = lean_array_push(v___x_313_, v___x_312_);
    return v___x_314_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__31() -> *mut leanh::LeanObject {
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__30_once),
        _init_l_Array_lex___auto__1___closed__30,
    );
    v___x_316_ = l_Array_lex___auto__1___closed__18;
    v___x_317_ = leanh::lean_box(2);
    v___x_318_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
    leanh::lean_ctor_set(v___x_318_, 1, v___x_316_);
    leanh::lean_ctor_set(v___x_318_, 2, v___x_315_);
    return v___x_318_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__32() -> *mut leanh::LeanObject {
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__31_once),
        _init_l_Array_lex___auto__1___closed__31,
    );
    v___x_320_ = l_Array_lex___auto__1___closed__5;
    v___x_321_ = lean_array_push(v___x_320_, v___x_319_);
    return v___x_321_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__38() -> *mut leanh::LeanObject {
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Array_lex___auto__1___closed__37;
    v___x_333_ = l_Lean_mkAtom(v___x_332_);
    return v___x_333_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__39() -> *mut leanh::LeanObject {
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__38_once),
        _init_l_Array_lex___auto__1___closed__38,
    );
    v___x_335_ = l_Array_lex___auto__1___closed__5;
    v___x_336_ = lean_array_push(v___x_335_, v___x_334_);
    return v___x_336_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__40() -> *mut leanh::LeanObject {
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_337_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__29_once),
        _init_l_Array_lex___auto__1___closed__29,
    );
    v___x_338_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__39_once),
        _init_l_Array_lex___auto__1___closed__39,
    );
    v___x_339_ = lean_array_push(v___x_338_, v___x_337_);
    return v___x_339_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__41() -> *mut leanh::LeanObject {
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__40_once),
        _init_l_Array_lex___auto__1___closed__40,
    );
    v___x_341_ = l_Array_lex___auto__1___closed__36;
    v___x_342_ = leanh::lean_box(2);
    v___x_343_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_343_, 0, v___x_342_);
    leanh::lean_ctor_set(v___x_343_, 1, v___x_341_);
    leanh::lean_ctor_set(v___x_343_, 2, v___x_340_);
    return v___x_343_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__42() -> *mut leanh::LeanObject {
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41_once),
        _init_l_Array_lex___auto__1___closed__41,
    );
    v___x_345_ = l_Array_lex___auto__1___closed__5;
    v___x_346_ = lean_array_push(v___x_345_, v___x_344_);
    return v___x_346_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__44() -> *mut leanh::LeanObject {
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = l_Array_lex___auto__1___closed__43;
    v___x_349_ = l_Lean_mkAtom(v___x_348_);
    return v___x_349_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__45() -> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__44_once),
        _init_l_Array_lex___auto__1___closed__44,
    );
    v___x_351_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__42_once),
        _init_l_Array_lex___auto__1___closed__42,
    );
    v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__46() -> *mut leanh::LeanObject {
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__41_once),
        _init_l_Array_lex___auto__1___closed__41,
    );
    v___x_354_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__45_once),
        _init_l_Array_lex___auto__1___closed__45,
    );
    v___x_355_ = lean_array_push(v___x_354_, v___x_353_);
    return v___x_355_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__47() -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__46_once),
        _init_l_Array_lex___auto__1___closed__46,
    );
    v___x_357_ = l_Array_lex___auto__1___closed__34;
    v___x_358_ = leanh::lean_box(2);
    v___x_359_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_359_, 0, v___x_358_);
    leanh::lean_ctor_set(v___x_359_, 1, v___x_357_);
    leanh::lean_ctor_set(v___x_359_, 2, v___x_356_);
    return v___x_359_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__48() -> *mut leanh::LeanObject {
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_360_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__47_once),
        _init_l_Array_lex___auto__1___closed__47,
    );
    v___x_361_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__32_once),
        _init_l_Array_lex___auto__1___closed__32,
    );
    v___x_362_ = lean_array_push(v___x_361_, v___x_360_);
    return v___x_362_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__50() -> *mut leanh::LeanObject {
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Array_lex___auto__1___closed__49;
    v___x_365_ = l_Lean_mkAtom(v___x_364_);
    return v___x_365_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__51() -> *mut leanh::LeanObject {
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__50_once),
        _init_l_Array_lex___auto__1___closed__50,
    );
    v___x_367_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__48_once),
        _init_l_Array_lex___auto__1___closed__48,
    );
    v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
    return v___x_368_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__52() -> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__51_once),
        _init_l_Array_lex___auto__1___closed__51,
    );
    v___x_370_ = l_Array_lex___auto__1___closed__16;
    v___x_371_ = leanh::lean_box(2);
    v___x_372_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
    leanh::lean_ctor_set(v___x_372_, 1, v___x_370_);
    leanh::lean_ctor_set(v___x_372_, 2, v___x_369_);
    return v___x_372_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__53() -> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__52_once),
        _init_l_Array_lex___auto__1___closed__52,
    );
    v___x_374_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__13_once),
        _init_l_Array_lex___auto__1___closed__13,
    );
    v___x_375_ = lean_array_push(v___x_374_, v___x_373_);
    return v___x_375_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__54() -> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__53_once),
        _init_l_Array_lex___auto__1___closed__53,
    );
    v___x_377_ = l_Array_lex___auto__1___closed__11;
    v___x_378_ = leanh::lean_box(2);
    v___x_379_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
    leanh::lean_ctor_set(v___x_379_, 1, v___x_377_);
    leanh::lean_ctor_set(v___x_379_, 2, v___x_376_);
    return v___x_379_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__55() -> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__54_once),
        _init_l_Array_lex___auto__1___closed__54,
    );
    v___x_381_ = l_Array_lex___auto__1___closed__5;
    v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
    return v___x_382_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__56() -> *mut leanh::LeanObject {
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__55_once),
        _init_l_Array_lex___auto__1___closed__55,
    );
    v___x_384_ = l_Array_lex___auto__1___closed__9;
    v___x_385_ = leanh::lean_box(2);
    v___x_386_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_386_, 0, v___x_385_);
    leanh::lean_ctor_set(v___x_386_, 1, v___x_384_);
    leanh::lean_ctor_set(v___x_386_, 2, v___x_383_);
    return v___x_386_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__57() -> *mut leanh::LeanObject {
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__56_once),
        _init_l_Array_lex___auto__1___closed__56,
    );
    v___x_388_ = l_Array_lex___auto__1___closed__5;
    v___x_389_ = lean_array_push(v___x_388_, v___x_387_);
    return v___x_389_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__58() -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__57_once),
        _init_l_Array_lex___auto__1___closed__57,
    );
    v___x_391_ = l_Array_lex___auto__1___closed__7;
    v___x_392_ = leanh::lean_box(2);
    v___x_393_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_393_, 0, v___x_392_);
    leanh::lean_ctor_set(v___x_393_, 1, v___x_391_);
    leanh::lean_ctor_set(v___x_393_, 2, v___x_390_);
    return v___x_393_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__59() -> *mut leanh::LeanObject {
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__58_once),
        _init_l_Array_lex___auto__1___closed__58,
    );
    v___x_395_ = l_Array_lex___auto__1___closed__5;
    v___x_396_ = lean_array_push(v___x_395_, v___x_394_);
    return v___x_396_;
}
pub unsafe fn _init_l_Array_lex___auto__1___closed__60() -> *mut leanh::LeanObject {
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__59),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__59_once),
        _init_l_Array_lex___auto__1___closed__59,
    );
    v___x_398_ = l_Array_lex___auto__1___closed__4;
    v___x_399_ = leanh::lean_box(2);
    v___x_400_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_400_, 0, v___x_399_);
    leanh::lean_ctor_set(v___x_400_, 1, v___x_398_);
    leanh::lean_ctor_set(v___x_400_, 2, v___x_397_);
    return v___x_400_;
}
pub unsafe fn _init_l_Array_lex___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__60),
        core::ptr::addr_of_mut!(l_Array_lex___auto__1___closed__60_once),
        _init_l_Array_lex___auto__1___closed__60,
    );
    return v___x_401_;
}
pub unsafe fn l_Array_lex___redArg___lam__0(
    mut v___y_402_: *mut leanh::LeanObject,
    mut v_as_403_: *mut leanh::LeanObject,
    mut v_bs_404_: *mut leanh::LeanObject,
    mut v_lt_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v___x_407_: *mut leanh::LeanObject,
    mut v___x_408_: *mut leanh::LeanObject,
    mut v_next_409_: *mut leanh::LeanObject,
    mut v_acc_410_: *mut leanh::LeanObject,
    mut v_h_411_: *mut leanh::LeanObject,
    mut v_G_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_413_: u8 = 0;
    v___x_413_ = lean_nat_dec_lt(v_next_409_, v___y_402_);
    if v___x_413_ == 0 {
        leanh::lean_dec_ref(v_G_412_);
        leanh::lean_dec_ref(v___x_408_);
        leanh::lean_dec_ref(v_inst_406_);
        leanh::lean_dec_ref(v_lt_405_);
        leanh::lean_inc_ref(v_acc_410_);
        return v_acc_410_;
    } else {
        let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: u8 = 0;
        v___x_414_ = lean_array_fget_borrowed(v_as_403_, v_next_409_);
        v___x_415_ = lean_array_fget_borrowed(v_bs_404_, v_next_409_);
        leanh::lean_inc(v___x_415_);
        leanh::lean_inc(v___x_414_);
        v___x_416_ = leanh::lean_apply_2(v_lt_405_, v___x_414_, v___x_415_);
        v___x_417_ = (leanh::lean_unbox(v___x_416_) as u8);
        if v___x_417_ == 0 {
            let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_419_: u8 = 0;
            leanh::lean_inc(v___x_415_);
            leanh::lean_inc(v___x_414_);
            v___x_418_ = leanh::lean_apply_2(v_inst_406_, v___x_414_, v___x_415_);
            v___x_419_ = (leanh::lean_unbox(v___x_418_) as u8);
            if v___x_419_ == 0 {
                let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_G_412_);
                leanh::lean_dec_ref(v___x_408_);
                v___x_420_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_420_, 0, v___x_416_);
                v___x_421_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_421_, 0, v___x_420_);
                leanh::lean_ctor_set(v___x_421_, 1, v___x_407_);
                return v___x_421_;
            } else {
                let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_422_ = leanh::lean_unsigned_to_nat(1);
                v___x_423_ = lean_nat_add(v_next_409_, v___x_422_);
                v___x_424_ = leanh::lean_apply_4(
                    v_G_412_,
                    v___x_423_,
                    v___x_408_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_424_;
            }
        } else {
            let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_G_412_);
            leanh::lean_dec_ref(v___x_408_);
            leanh::lean_dec_ref(v_inst_406_);
            v___x_425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_425_, 0, v___x_416_);
            v___x_426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_426_, 0, v___x_425_);
            leanh::lean_ctor_set(v___x_426_, 1, v___x_407_);
            return v___x_426_;
        }
    }
}
pub unsafe fn l_Array_lex___redArg___lam__0___boxed(
    mut v___y_427_: *mut leanh::LeanObject,
    mut v_as_428_: *mut leanh::LeanObject,
    mut v_bs_429_: *mut leanh::LeanObject,
    mut v_lt_430_: *mut leanh::LeanObject,
    mut v_inst_431_: *mut leanh::LeanObject,
    mut v___x_432_: *mut leanh::LeanObject,
    mut v___x_433_: *mut leanh::LeanObject,
    mut v_next_434_: *mut leanh::LeanObject,
    mut v_acc_435_: *mut leanh::LeanObject,
    mut v_h_436_: *mut leanh::LeanObject,
    mut v_G_437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_438_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_acc_435_);
    leanh::lean_dec(v_next_434_);
    leanh::lean_dec_ref(v_bs_429_);
    leanh::lean_dec_ref(v_as_428_);
    leanh::lean_dec(v___y_427_);
    return v_res_438_;
}
pub unsafe fn l_Array_lex___redArg(
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_as_443_: *mut leanh::LeanObject,
    mut v_bs_444_: *mut leanh::LeanObject,
    mut v_lt_445_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    let mut v_val_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v___x_459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_446_ = leanh::lean_unsigned_to_nat(0);
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
                v___x_451_ = leanh::lean_box(0);
                v___x_452_ = l_Array_lex___redArg___closed__0;
                v___f_453_ = leanh::lean_alloc_closure(
                    l_Array_lex___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                leanh::lean_closure_set(v___f_453_, 0, v___y_450_);
                leanh::lean_closure_set(v___f_453_, 1, v_as_443_);
                leanh::lean_closure_set(v___f_453_, 2, v_bs_444_);
                leanh::lean_closure_set(v___f_453_, 3, v_lt_445_);
                leanh::lean_closure_set(v___f_453_, 4, v_inst_442_);
                leanh::lean_closure_set(v___f_453_, 5, v___x_451_);
                leanh::lean_closure_set(v___f_453_, 6, v___x_452_);
                v___x_454_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_453_,
                    v___x_446_,
                    v___x_452_,
                    leanh::lean_box(0),
                );
                v_fst_455_ = leanh::lean_ctor_get(v___x_454_, 0);
                leanh::lean_inc(v_fst_455_);
                leanh::lean_dec(v___x_454_);
                if leanh::lean_obj_tag(v_fst_455_) == 0 {
                    v___x_456_ = lean_nat_dec_lt(v___x_447_, v___x_448_);
                    return v___x_456_;
                } else {
                    v_val_457_ = leanh::lean_ctor_get(v_fst_455_, 0);
                    leanh::lean_inc(v_val_457_);
                    leanh::lean_dec_ref_known(v_fst_455_, 1);
                    v___x_458_ = (leanh::lean_unbox(v_val_457_) as u8);
                    leanh::lean_dec(v_val_457_);
                    return v___x_458_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_lex___redArg___boxed(
    mut v_inst_460_: *mut leanh::LeanObject,
    mut v_as_461_: *mut leanh::LeanObject,
    mut v_bs_462_: *mut leanh::LeanObject,
    mut v_lt_463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_464_: u8 = 0;
    let mut v_r_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Array_lex___redArg(v_inst_460_, v_as_461_, v_bs_462_, v_lt_463_);
    v_r_465_ = leanh::lean_box((v_res_464_) as usize);
    return v_r_465_;
}
pub unsafe fn l_Array_lex(
    mut v_00_u03b1_466_: *mut leanh::LeanObject,
    mut v_inst_467_: *mut leanh::LeanObject,
    mut v_as_468_: *mut leanh::LeanObject,
    mut v_bs_469_: *mut leanh::LeanObject,
    mut v_lt_470_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_471_: u8 = 0;
    v___x_471_ = l_Array_lex___redArg(v_inst_467_, v_as_468_, v_bs_469_, v_lt_470_);
    return v___x_471_;
}
pub unsafe fn l_Array_lex___boxed(
    mut v_00_u03b1_472_: *mut leanh::LeanObject,
    mut v_inst_473_: *mut leanh::LeanObject,
    mut v_as_474_: *mut leanh::LeanObject,
    mut v_bs_475_: *mut leanh::LeanObject,
    mut v_lt_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_477_: u8 = 0;
    let mut v_r_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Array_lex(
        v_00_u03b1_472_,
        v_inst_473_,
        v_as_474_,
        v_bs_475_,
        v_lt_476_,
    );
    v_r_478_ = leanh::lean_box((v_res_477_) as usize);
    return v_r_478_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Lex_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Array_Lex_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_lex___auto__1 = _init_l_Array_lex___auto__1();
    leanh::lean_mark_persistent(l_Array_lex___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Lex_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Lex_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Lex_Basic(builtin);
}