// Lean compiler output
// Module: Init.Data.List.Sort.Basic
// Imports: Init.Ext Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Data.Nat.Lemmas Init.Omega
use crate::ffi::{
    lean_array_push, lean_nat_add, lean_nat_dec_le, lean_nat_shiftr, lean_string_utf8_byte_size,
};
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
use crate::r#gen::Init::Prelude::{l_Lean_mkAtom, l_List_lengthTR___redArg};
pub static l_List_merge___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_merge___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_List_merge___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_List_merge___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_List_merge___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_List_merge___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_merge___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_List_merge___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_List_merge___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l_List_merge___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_merge___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_merge___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
static mut l_List_merge___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_List_merge___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_merge___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__14_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_merge___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__15_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_List_merge___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__15_value) as *mut crate::leanh::LeanObject;
static l_List_merge___auto__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_merge___auto__1___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__15_value)
                as *mut crate::leanh::LeanObject,
            7043493786777132025 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__19_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_List_merge___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__19_value) as *mut crate::leanh::LeanObject;
static l_List_merge___auto__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_merge___auto__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_merge___auto__1___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__19_value)
                as *mut crate::leanh::LeanObject,
            16077784126176397009 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__21_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [97, 0],
    };
static mut l_List_merge___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__24_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__21_value)
                as *mut crate::leanh::LeanObject,
            7839396180116328695 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__27_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [98, 0],
    };
static mut l_List_merge___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__27_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__30_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__27_value)
                as *mut crate::leanh::LeanObject,
            10300200614825825839 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__35_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_merge___auto__1___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__35_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__37_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_List_merge___auto__1___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__37_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_merge___auto__1___closed__40_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_List_merge___auto__1___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__41_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_merge___auto__1___closed__40_value)
                as *mut crate::leanh::LeanObject,
            8748957123817046895 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_merge___auto__1___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_List_merge___auto__1___closed__42_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_List_merge___auto__1___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_merge___auto__1___closed__42_value) as *mut crate::leanh::LeanObject;
static mut l_List_merge___auto__1___closed__43_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__46_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__47_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__48_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__49_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__50_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__51_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__52_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__53_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__54_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__55_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__56_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__57_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_merge___auto__1___closed__58_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_merge___auto__1___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_List_merge___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_List_mergeSort___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_List_merge___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = l_List_merge___auto__1___closed__10;
    v___x_349_ = l_Lean_mkAtom(v___x_348_);
    return v___x_349_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__12_once),
        _init_l_List_merge___auto__1___closed__12,
    );
    v___x_351_ = l_List_merge___auto__1___closed__5;
    v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_360_ = l_List_merge___auto__1___closed__15;
    v___x_361_ = l_Lean_mkAtom(v___x_360_);
    return v___x_361_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__17_once),
        _init_l_List_merge___auto__1___closed__17,
    );
    v___x_363_ = l_List_merge___auto__1___closed__5;
    v___x_364_ = lean_array_push(v___x_363_, v___x_362_);
    return v___x_364_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = l_List_merge___auto__1___closed__21;
    v___x_373_ = lean_string_utf8_byte_size(v___x_372_);
    return v___x_373_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__22_once),
        _init_l_List_merge___auto__1___closed__22,
    );
    v___x_375_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_376_ = l_List_merge___auto__1___closed__21;
    v___x_377_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_377_, 0, v___x_376_);
    crate::leanh::lean_ctor_set(v___x_377_, 1, v___x_375_);
    crate::leanh::lean_ctor_set(v___x_377_, 2, v___x_374_);
    return v___x_377_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = crate::leanh::lean_box(0);
    v___x_381_ = l_List_merge___auto__1___closed__24;
    v___x_382_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__23_once),
        _init_l_List_merge___auto__1___closed__23,
    );
    v___x_383_ = crate::leanh::lean_box(2);
    v___x_384_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_384_, 0, v___x_383_);
    crate::leanh::lean_ctor_set(v___x_384_, 1, v___x_382_);
    crate::leanh::lean_ctor_set(v___x_384_, 2, v___x_381_);
    crate::leanh::lean_ctor_set(v___x_384_, 3, v___x_380_);
    return v___x_384_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__25_once),
        _init_l_List_merge___auto__1___closed__25,
    );
    v___x_386_ = l_List_merge___auto__1___closed__5;
    v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
    return v___x_387_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = l_List_merge___auto__1___closed__27;
    v___x_390_ = lean_string_utf8_byte_size(v___x_389_);
    return v___x_390_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__28_once),
        _init_l_List_merge___auto__1___closed__28,
    );
    v___x_392_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_393_ = l_List_merge___auto__1___closed__27;
    v___x_394_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_394_, 0, v___x_393_);
    crate::leanh::lean_ctor_set(v___x_394_, 1, v___x_392_);
    crate::leanh::lean_ctor_set(v___x_394_, 2, v___x_391_);
    return v___x_394_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__31() -> *mut crate::leanh::LeanObject {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = crate::leanh::lean_box(0);
    v___x_398_ = l_List_merge___auto__1___closed__30;
    v___x_399_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__29_once),
        _init_l_List_merge___auto__1___closed__29,
    );
    v___x_400_ = crate::leanh::lean_box(2);
    v___x_401_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_401_, 0, v___x_400_);
    crate::leanh::lean_ctor_set(v___x_401_, 1, v___x_399_);
    crate::leanh::lean_ctor_set(v___x_401_, 2, v___x_398_);
    crate::leanh::lean_ctor_set(v___x_401_, 3, v___x_397_);
    return v___x_401_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31_once),
        _init_l_List_merge___auto__1___closed__31,
    );
    v___x_403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26_once),
        _init_l_List_merge___auto__1___closed__26,
    );
    v___x_404_ = lean_array_push(v___x_403_, v___x_402_);
    return v___x_404_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__33() -> *mut crate::leanh::LeanObject {
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__32_once),
        _init_l_List_merge___auto__1___closed__32,
    );
    v___x_406_ = l_List_merge___auto__1___closed__9;
    v___x_407_ = crate::leanh::lean_box(2);
    v___x_408_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_408_, 0, v___x_407_);
    crate::leanh::lean_ctor_set(v___x_408_, 1, v___x_406_);
    crate::leanh::lean_ctor_set(v___x_408_, 2, v___x_405_);
    return v___x_408_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__34() -> *mut crate::leanh::LeanObject {
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_409_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__33_once),
        _init_l_List_merge___auto__1___closed__33,
    );
    v___x_410_ = l_List_merge___auto__1___closed__5;
    v___x_411_ = lean_array_push(v___x_410_, v___x_409_);
    return v___x_411_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__36() -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = l_List_merge___auto__1___closed__35;
    v___x_417_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__34_once),
        _init_l_List_merge___auto__1___closed__34,
    );
    v___x_418_ = lean_array_push(v___x_417_, v___x_416_);
    return v___x_418_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__38() -> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = l_List_merge___auto__1___closed__37;
    v___x_421_ = l_Lean_mkAtom(v___x_420_);
    return v___x_421_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__39() -> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__38_once),
        _init_l_List_merge___auto__1___closed__38,
    );
    v___x_423_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__36_once),
        _init_l_List_merge___auto__1___closed__36,
    );
    v___x_424_ = lean_array_push(v___x_423_, v___x_422_);
    return v___x_424_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__43() -> *mut crate::leanh::LeanObject {
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = l_List_merge___auto__1___closed__42;
    v___x_430_ = l_Lean_mkAtom(v___x_429_);
    return v___x_430_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__44() -> *mut crate::leanh::LeanObject {
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__43_once),
        _init_l_List_merge___auto__1___closed__43,
    );
    v___x_432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__26_once),
        _init_l_List_merge___auto__1___closed__26,
    );
    v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
    return v___x_433_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__45() -> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__31_once),
        _init_l_List_merge___auto__1___closed__31,
    );
    v___x_435_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__44_once),
        _init_l_List_merge___auto__1___closed__44,
    );
    v___x_436_ = lean_array_push(v___x_435_, v___x_434_);
    return v___x_436_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__46() -> *mut crate::leanh::LeanObject {
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__45_once),
        _init_l_List_merge___auto__1___closed__45,
    );
    v___x_438_ = l_List_merge___auto__1___closed__41;
    v___x_439_ = crate::leanh::lean_box(2);
    v___x_440_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_440_, 0, v___x_439_);
    crate::leanh::lean_ctor_set(v___x_440_, 1, v___x_438_);
    crate::leanh::lean_ctor_set(v___x_440_, 2, v___x_437_);
    return v___x_440_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__47() -> *mut crate::leanh::LeanObject {
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__46_once),
        _init_l_List_merge___auto__1___closed__46,
    );
    v___x_442_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__39_once),
        _init_l_List_merge___auto__1___closed__39,
    );
    v___x_443_ = lean_array_push(v___x_442_, v___x_441_);
    return v___x_443_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__48() -> *mut crate::leanh::LeanObject {
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_444_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__47_once),
        _init_l_List_merge___auto__1___closed__47,
    );
    v___x_445_ = l_List_merge___auto__1___closed__20;
    v___x_446_ = crate::leanh::lean_box(2);
    v___x_447_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_447_, 0, v___x_446_);
    crate::leanh::lean_ctor_set(v___x_447_, 1, v___x_445_);
    crate::leanh::lean_ctor_set(v___x_447_, 2, v___x_444_);
    return v___x_447_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__49() -> *mut crate::leanh::LeanObject {
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__48_once),
        _init_l_List_merge___auto__1___closed__48,
    );
    v___x_449_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__18_once),
        _init_l_List_merge___auto__1___closed__18,
    );
    v___x_450_ = lean_array_push(v___x_449_, v___x_448_);
    return v___x_450_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__50() -> *mut crate::leanh::LeanObject {
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_451_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__49),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__49_once),
        _init_l_List_merge___auto__1___closed__49,
    );
    v___x_452_ = l_List_merge___auto__1___closed__16;
    v___x_453_ = crate::leanh::lean_box(2);
    v___x_454_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_454_, 0, v___x_453_);
    crate::leanh::lean_ctor_set(v___x_454_, 1, v___x_452_);
    crate::leanh::lean_ctor_set(v___x_454_, 2, v___x_451_);
    return v___x_454_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__51() -> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__50_once),
        _init_l_List_merge___auto__1___closed__50,
    );
    v___x_456_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__13_once),
        _init_l_List_merge___auto__1___closed__13,
    );
    v___x_457_ = lean_array_push(v___x_456_, v___x_455_);
    return v___x_457_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__52() -> *mut crate::leanh::LeanObject {
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__51_once),
        _init_l_List_merge___auto__1___closed__51,
    );
    v___x_459_ = l_List_merge___auto__1___closed__11;
    v___x_460_ = crate::leanh::lean_box(2);
    v___x_461_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_461_, 0, v___x_460_);
    crate::leanh::lean_ctor_set(v___x_461_, 1, v___x_459_);
    crate::leanh::lean_ctor_set(v___x_461_, 2, v___x_458_);
    return v___x_461_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__53() -> *mut crate::leanh::LeanObject {
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_462_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__52_once),
        _init_l_List_merge___auto__1___closed__52,
    );
    v___x_463_ = l_List_merge___auto__1___closed__5;
    v___x_464_ = lean_array_push(v___x_463_, v___x_462_);
    return v___x_464_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__54() -> *mut crate::leanh::LeanObject {
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__53_once),
        _init_l_List_merge___auto__1___closed__53,
    );
    v___x_466_ = l_List_merge___auto__1___closed__9;
    v___x_467_ = crate::leanh::lean_box(2);
    v___x_468_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_468_, 0, v___x_467_);
    crate::leanh::lean_ctor_set(v___x_468_, 1, v___x_466_);
    crate::leanh::lean_ctor_set(v___x_468_, 2, v___x_465_);
    return v___x_468_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__55() -> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__54_once),
        _init_l_List_merge___auto__1___closed__54,
    );
    v___x_470_ = l_List_merge___auto__1___closed__5;
    v___x_471_ = lean_array_push(v___x_470_, v___x_469_);
    return v___x_471_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__56() -> *mut crate::leanh::LeanObject {
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__55_once),
        _init_l_List_merge___auto__1___closed__55,
    );
    v___x_473_ = l_List_merge___auto__1___closed__7;
    v___x_474_ = crate::leanh::lean_box(2);
    v___x_475_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_475_, 0, v___x_474_);
    crate::leanh::lean_ctor_set(v___x_475_, 1, v___x_473_);
    crate::leanh::lean_ctor_set(v___x_475_, 2, v___x_472_);
    return v___x_475_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__57() -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__56_once),
        _init_l_List_merge___auto__1___closed__56,
    );
    v___x_477_ = l_List_merge___auto__1___closed__5;
    v___x_478_ = lean_array_push(v___x_477_, v___x_476_);
    return v___x_478_;
}
pub unsafe fn _init_l_List_merge___auto__1___closed__58() -> *mut crate::leanh::LeanObject {
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__57_once),
        _init_l_List_merge___auto__1___closed__57,
    );
    v___x_480_ = l_List_merge___auto__1___closed__4;
    v___x_481_ = crate::leanh::lean_box(2);
    v___x_482_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_482_, 0, v___x_481_);
    crate::leanh::lean_ctor_set(v___x_482_, 1, v___x_480_);
    crate::leanh::lean_ctor_set(v___x_482_, 2, v___x_479_);
    return v___x_482_;
}
pub unsafe fn _init_l_List_merge___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58_once),
        _init_l_List_merge___auto__1___closed__58,
    );
    return v___x_483_;
}
pub unsafe fn l_List_merge___redArg(
    mut v_xs_484_: *mut crate::leanh::LeanObject,
    mut v_ys_485_: *mut crate::leanh::LeanObject,
    mut v_le_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: u8 = 0;
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_495_: u8 = 0;
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_500_: u8 = 0;
    let mut v_unused_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut v_unused_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_xs_484_) == 0 {
                    crate::leanh::lean_dec_ref(v_le_486_);
                    return v_ys_485_;
                } else {
                    if crate::leanh::lean_obj_tag(v_ys_485_) == 0 {
                        crate::leanh::lean_dec_ref(v_le_486_);
                        return v_xs_484_;
                    } else {
                        v_head_487_ = crate::leanh::lean_ctor_get(v_xs_484_, 0);
                        v_tail_488_ = crate::leanh::lean_ctor_get(v_xs_484_, 1);
                        v_head_489_ = crate::leanh::lean_ctor_get(v_ys_485_, 0);
                        v_tail_490_ = crate::leanh::lean_ctor_get(v_ys_485_, 1);
                        crate::leanh::lean_inc_ref(v_le_486_);
                        crate::leanh::lean_inc(v_head_489_);
                        crate::leanh::lean_inc(v_head_487_);
                        v___x_491_ =
                            crate::leanh::lean_apply_2(v_le_486_, v_head_487_, v_head_489_);
                        v___x_492_ = (crate::leanh::lean_unbox(v___x_491_) as u8);
                        if v___x_492_ == 0 {
                            crate::leanh::lean_inc(v_tail_490_);
                            crate::leanh::lean_inc(v_head_489_);
                            v_isSharedCheck_500_ =
                                (!crate::leanh::lean_is_exclusive(v_ys_485_)) as u8;
                            if v_isSharedCheck_500_ == 0 {
                                v_unused_501_ = crate::leanh::lean_ctor_get(v_ys_485_, 1);
                                crate::leanh::lean_dec(v_unused_501_);
                                v_unused_502_ = crate::leanh::lean_ctor_get(v_ys_485_, 0);
                                crate::leanh::lean_dec(v_unused_502_);
                                v___x_494_ = v_ys_485_;
                                v_isShared_495_ = v_isSharedCheck_500_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_ys_485_);
                                v___x_494_ = crate::leanh::lean_box(0);
                                v_isShared_495_ = v_isSharedCheck_500_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc(v_tail_488_);
                            crate::leanh::lean_inc(v_head_487_);
                            v_isSharedCheck_510_ =
                                (!crate::leanh::lean_is_exclusive(v_xs_484_)) as u8;
                            if v_isSharedCheck_510_ == 0 {
                                v_unused_511_ = crate::leanh::lean_ctor_get(v_xs_484_, 1);
                                crate::leanh::lean_dec(v_unused_511_);
                                v_unused_512_ = crate::leanh::lean_ctor_get(v_xs_484_, 0);
                                crate::leanh::lean_dec(v_unused_512_);
                                v___x_504_ = v_xs_484_;
                                v_isShared_505_ = v_isSharedCheck_510_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_xs_484_);
                                v___x_504_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_494_, 1, v___x_496_);
                    v___x_498_ = v___x_494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_499_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_499_, 0, v_head_489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
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
                    crate::leanh::lean_ctor_set(v___x_504_, 1, v___x_506_);
                    v___x_508_ = v___x_504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v_head_487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_506_);
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
    mut v_00_u03b1_513_: *mut crate::leanh::LeanObject,
    mut v_xs_514_: *mut crate::leanh::LeanObject,
    mut v_ys_515_: *mut crate::leanh::LeanObject,
    mut v_le_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = l_List_merge___redArg(v_xs_514_, v_ys_515_, v_le_516_);
    return v___x_517_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter___redArg(
    mut v_xs_518_: *mut crate::leanh::LeanObject,
    mut v_ys_519_: *mut crate::leanh::LeanObject,
    mut v_h__1_520_: *mut crate::leanh::LeanObject,
    mut v_h__2_521_: *mut crate::leanh::LeanObject,
    mut v_h__3_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_518_) == 0 {
        let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_522_);
        crate::leanh::lean_dec(v_h__2_521_);
        v___x_523_ = crate::leanh::lean_apply_1(v_h__1_520_, v_ys_519_);
        return v___x_523_;
    } else {
        crate::leanh::lean_dec(v_h__1_520_);
        if crate::leanh::lean_obj_tag(v_ys_519_) == 0 {
            let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_522_);
            v___x_524_ =
                crate::leanh::lean_apply_2(v_h__2_521_, v_xs_518_, crate::leanh::lean_box(0));
            return v___x_524_;
        } else {
            let mut v_head_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_521_);
            v_head_525_ = crate::leanh::lean_ctor_get(v_xs_518_, 0);
            crate::leanh::lean_inc(v_head_525_);
            v_tail_526_ = crate::leanh::lean_ctor_get(v_xs_518_, 1);
            crate::leanh::lean_inc(v_tail_526_);
            crate::leanh::lean_dec_ref_known(v_xs_518_, 2);
            v_head_527_ = crate::leanh::lean_ctor_get(v_ys_519_, 0);
            crate::leanh::lean_inc(v_head_527_);
            v_tail_528_ = crate::leanh::lean_ctor_get(v_ys_519_, 1);
            crate::leanh::lean_inc(v_tail_528_);
            crate::leanh::lean_dec_ref_known(v_ys_519_, 2);
            v___x_529_ = crate::leanh::lean_apply_4(
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
    mut v_00_u03b1_530_: *mut crate::leanh::LeanObject,
    mut v_motive_531_: *mut crate::leanh::LeanObject,
    mut v_xs_532_: *mut crate::leanh::LeanObject,
    mut v_ys_533_: *mut crate::leanh::LeanObject,
    mut v_h__1_534_: *mut crate::leanh::LeanObject,
    mut v_h__2_535_: *mut crate::leanh::LeanObject,
    mut v_h__3_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_532_) == 0 {
        let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_536_);
        crate::leanh::lean_dec(v_h__2_535_);
        v___x_537_ = crate::leanh::lean_apply_1(v_h__1_534_, v_ys_533_);
        return v___x_537_;
    } else {
        crate::leanh::lean_dec(v_h__1_534_);
        if crate::leanh::lean_obj_tag(v_ys_533_) == 0 {
            let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_536_);
            v___x_538_ =
                crate::leanh::lean_apply_2(v_h__2_535_, v_xs_532_, crate::leanh::lean_box(0));
            return v___x_538_;
        } else {
            let mut v_head_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_535_);
            v_head_539_ = crate::leanh::lean_ctor_get(v_xs_532_, 0);
            crate::leanh::lean_inc(v_head_539_);
            v_tail_540_ = crate::leanh::lean_ctor_get(v_xs_532_, 1);
            crate::leanh::lean_inc(v_tail_540_);
            crate::leanh::lean_dec_ref_known(v_xs_532_, 2);
            v_head_541_ = crate::leanh::lean_ctor_get(v_ys_533_, 0);
            crate::leanh::lean_inc(v_head_541_);
            v_tail_542_ = crate::leanh::lean_ctor_get(v_ys_533_, 1);
            crate::leanh::lean_inc(v_tail_542_);
            crate::leanh::lean_dec_ref_known(v_ys_533_, 2);
            v___x_543_ = crate::leanh::lean_apply_4(
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
    mut v_n_544_: *mut crate::leanh::LeanObject,
    mut v_l_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_554_: u8 = 0;
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_546_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_547_ = lean_nat_add(v_n_544_, v___x_546_);
                v___x_548_ = lean_nat_shiftr(v___x_547_, v___x_546_);
                crate::leanh::lean_dec(v___x_547_);
                v_r_549_ = l_List_splitAt___redArg(v___x_548_, v_l_545_);
                v_fst_550_ = crate::leanh::lean_ctor_get(v_r_549_, 0);
                v_snd_551_ = crate::leanh::lean_ctor_get(v_r_549_, 1);
                v_isSharedCheck_558_ = (!crate::leanh::lean_is_exclusive(v_r_549_)) as u8;
                if v_isSharedCheck_558_ == 0 {
                    v___x_553_ = v_r_549_;
                    v_isShared_554_ = v_isSharedCheck_558_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_551_);
                    crate::leanh::lean_inc(v_fst_550_);
                    crate::leanh::lean_dec(v_r_549_);
                    v___x_553_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_557_, 0, v_fst_550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_557_, 1, v_snd_551_);
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
    mut v_n_559_: *mut crate::leanh::LeanObject,
    mut v_l_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_561_ = l_List_MergeSort_Internal_splitInTwo___redArg(v_n_559_, v_l_560_);
    crate::leanh::lean_dec(v_n_559_);
    return v_res_561_;
}
pub unsafe fn l_List_MergeSort_Internal_splitInTwo(
    mut v_00_u03b1_562_: *mut crate::leanh::LeanObject,
    mut v_n_563_: *mut crate::leanh::LeanObject,
    mut v_l_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = l_List_MergeSort_Internal_splitInTwo___redArg(v_n_563_, v_l_564_);
    return v___x_565_;
}
pub unsafe fn l_List_MergeSort_Internal_splitInTwo___boxed(
    mut v_00_u03b1_566_: *mut crate::leanh::LeanObject,
    mut v_n_567_: *mut crate::leanh::LeanObject,
    mut v_l_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_569_ = l_List_MergeSort_Internal_splitInTwo(v_00_u03b1_566_, v_n_567_, v_l_568_);
    crate::leanh::lean_dec(v_n_567_);
    return v_res_569_;
}
pub unsafe fn _init_l_List_mergeSort___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_570_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_merge___auto__1___closed__58_once),
        _init_l_List_merge___auto__1___closed__58,
    );
    return v___x_570_;
}
pub unsafe fn l_List_mergeSort___redArg(
    mut v_x_571_: *mut crate::leanh::LeanObject,
    mut v_x_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_571_) == 0 {
        crate::leanh::lean_dec_ref(v_x_572_);
        return v_x_571_;
    } else {
        let mut v_tail_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_573_ = crate::leanh::lean_ctor_get(v_x_571_, 1);
        if crate::leanh::lean_obj_tag(v_tail_573_) == 0 {
            crate::leanh::lean_dec_ref(v_x_572_);
            return v_x_571_;
        } else {
            let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lr_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_574_ = l_List_lengthTR___redArg(v_x_571_);
            v_lr_575_ = l_List_MergeSort_Internal_splitInTwo___redArg(v___x_574_, v_x_571_);
            crate::leanh::lean_dec(v___x_574_);
            v_fst_576_ = crate::leanh::lean_ctor_get(v_lr_575_, 0);
            crate::leanh::lean_inc(v_fst_576_);
            v_snd_577_ = crate::leanh::lean_ctor_get(v_lr_575_, 1);
            crate::leanh::lean_inc(v_snd_577_);
            crate::leanh::lean_dec_ref(v_lr_575_);
            crate::leanh::lean_inc_ref_n(v_x_572_, 2);
            v___x_578_ = l_List_mergeSort___redArg(v_fst_576_, v_x_572_);
            v___x_579_ = l_List_mergeSort___redArg(v_snd_577_, v_x_572_);
            v___x_580_ = l_List_merge___redArg(v___x_578_, v___x_579_, v_x_572_);
            return v___x_580_;
        }
    }
}
pub unsafe fn l_List_mergeSort(
    mut v_00_u03b1_581_: *mut crate::leanh::LeanObject,
    mut v_x_582_: *mut crate::leanh::LeanObject,
    mut v_x_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = l_List_mergeSort___redArg(v_x_582_, v_x_583_);
    return v___x_584_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_585_: *mut crate::leanh::LeanObject,
    mut v_x_586_: *mut crate::leanh::LeanObject,
    mut v_h__1_587_: *mut crate::leanh::LeanObject,
    mut v_h__2_588_: *mut crate::leanh::LeanObject,
    mut v_h__3_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_585_) == 0 {
        let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_589_);
        crate::leanh::lean_dec(v_h__2_588_);
        v___x_590_ = crate::leanh::lean_apply_1(v_h__1_587_, v_x_586_);
        return v___x_590_;
    } else {
        let mut v_tail_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_587_);
        v_tail_591_ = crate::leanh::lean_ctor_get(v_x_585_, 1);
        if crate::leanh::lean_obj_tag(v_tail_591_) == 0 {
            let mut v_head_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_589_);
            v_head_592_ = crate::leanh::lean_ctor_get(v_x_585_, 0);
            crate::leanh::lean_inc(v_head_592_);
            crate::leanh::lean_dec_ref_known(v_x_585_, 2);
            v___x_593_ = crate::leanh::lean_apply_2(v_h__2_588_, v_head_592_, v_x_586_);
            return v___x_593_;
        } else {
            let mut v_head_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_591_);
            crate::leanh::lean_dec(v_h__2_588_);
            v_head_594_ = crate::leanh::lean_ctor_get(v_x_585_, 0);
            crate::leanh::lean_inc(v_head_594_);
            crate::leanh::lean_dec_ref_known(v_x_585_, 2);
            v_head_595_ = crate::leanh::lean_ctor_get(v_tail_591_, 0);
            crate::leanh::lean_inc(v_head_595_);
            v_tail_596_ = crate::leanh::lean_ctor_get(v_tail_591_, 1);
            crate::leanh::lean_inc(v_tail_596_);
            crate::leanh::lean_dec_ref_known(v_tail_591_, 2);
            v___x_597_ = crate::leanh::lean_apply_4(
                v_h__3_589_,
                v_head_594_,
                v_head_595_,
                v_tail_596_,
                v_x_586_,
            );
            return v___x_597_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Basic_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_598_: *mut crate::leanh::LeanObject,
    mut v_motive_599_: *mut crate::leanh::LeanObject,
    mut v_x_600_: *mut crate::leanh::LeanObject,
    mut v_x_601_: *mut crate::leanh::LeanObject,
    mut v_h__1_602_: *mut crate::leanh::LeanObject,
    mut v_h__2_603_: *mut crate::leanh::LeanObject,
    mut v_h__3_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_600_) == 0 {
        let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_604_);
        crate::leanh::lean_dec(v_h__2_603_);
        v___x_605_ = crate::leanh::lean_apply_1(v_h__1_602_, v_x_601_);
        return v___x_605_;
    } else {
        let mut v_tail_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_602_);
        v_tail_606_ = crate::leanh::lean_ctor_get(v_x_600_, 1);
        if crate::leanh::lean_obj_tag(v_tail_606_) == 0 {
            let mut v_head_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_604_);
            v_head_607_ = crate::leanh::lean_ctor_get(v_x_600_, 0);
            crate::leanh::lean_inc(v_head_607_);
            crate::leanh::lean_dec_ref_known(v_x_600_, 2);
            v___x_608_ = crate::leanh::lean_apply_2(v_h__2_603_, v_head_607_, v_x_601_);
            return v___x_608_;
        } else {
            let mut v_head_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_606_);
            crate::leanh::lean_dec(v_h__2_603_);
            v_head_609_ = crate::leanh::lean_ctor_get(v_x_600_, 0);
            crate::leanh::lean_inc(v_head_609_);
            crate::leanh::lean_dec_ref_known(v_x_600_, 2);
            v_head_610_ = crate::leanh::lean_ctor_get(v_tail_606_, 0);
            crate::leanh::lean_inc(v_head_610_);
            v_tail_611_ = crate::leanh::lean_ctor_get(v_tail_606_, 1);
            crate::leanh::lean_inc(v_tail_611_);
            crate::leanh::lean_dec_ref_known(v_tail_606_, 2);
            v___x_612_ = crate::leanh::lean_apply_4(
                v_h__3_604_,
                v_head_609_,
                v_head_610_,
                v_tail_611_,
                v_x_601_,
            );
            return v___x_612_;
        }
    }
}
pub unsafe fn l_List_zipIdxLE___redArg(
    mut v_le_613_: *mut crate::leanh::LeanObject,
    mut v_a_614_: *mut crate::leanh::LeanObject,
    mut v_b_615_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    v_fst_616_ = crate::leanh::lean_ctor_get(v_a_614_, 0);
    crate::leanh::lean_inc_n(v_fst_616_, 2);
    v_snd_617_ = crate::leanh::lean_ctor_get(v_a_614_, 1);
    crate::leanh::lean_inc(v_snd_617_);
    crate::leanh::lean_dec_ref(v_a_614_);
    v_fst_618_ = crate::leanh::lean_ctor_get(v_b_615_, 0);
    crate::leanh::lean_inc_n(v_fst_618_, 2);
    v_snd_619_ = crate::leanh::lean_ctor_get(v_b_615_, 1);
    crate::leanh::lean_inc(v_snd_619_);
    crate::leanh::lean_dec_ref(v_b_615_);
    crate::leanh::lean_inc_ref(v_le_613_);
    v___x_620_ = crate::leanh::lean_apply_2(v_le_613_, v_fst_616_, v_fst_618_);
    v___x_621_ = (crate::leanh::lean_unbox(v___x_620_) as u8);
    if v___x_621_ == 0 {
        let mut v___x_622_: u8 = 0;
        crate::leanh::lean_dec(v_snd_619_);
        crate::leanh::lean_dec(v_fst_618_);
        crate::leanh::lean_dec(v_snd_617_);
        crate::leanh::lean_dec(v_fst_616_);
        crate::leanh::lean_dec_ref(v_le_613_);
        v___x_622_ = (crate::leanh::lean_unbox(v___x_620_) as u8);
        return v___x_622_;
    } else {
        let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_624_: u8 = 0;
        v___x_623_ = crate::leanh::lean_apply_2(v_le_613_, v_fst_618_, v_fst_616_);
        v___x_624_ = (crate::leanh::lean_unbox(v___x_623_) as u8);
        if v___x_624_ == 0 {
            let mut v___x_625_: u8 = 0;
            crate::leanh::lean_dec(v_snd_619_);
            crate::leanh::lean_dec(v_snd_617_);
            v___x_625_ = (crate::leanh::lean_unbox(v___x_620_) as u8);
            return v___x_625_;
        } else {
            let mut v___x_626_: u8 = 0;
            v___x_626_ = lean_nat_dec_le(v_snd_617_, v_snd_619_);
            crate::leanh::lean_dec(v_snd_619_);
            crate::leanh::lean_dec(v_snd_617_);
            return v___x_626_;
        }
    }
}
pub unsafe fn l_List_zipIdxLE___redArg___boxed(
    mut v_le_627_: *mut crate::leanh::LeanObject,
    mut v_a_628_: *mut crate::leanh::LeanObject,
    mut v_b_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_630_: u8 = 0;
    let mut v_r_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ = l_List_zipIdxLE___redArg(v_le_627_, v_a_628_, v_b_629_);
    v_r_631_ = crate::leanh::lean_box((v_res_630_) as usize);
    return v_r_631_;
}
pub unsafe fn l_List_zipIdxLE(
    mut v_00_u03b1_632_: *mut crate::leanh::LeanObject,
    mut v_le_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_b_635_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_636_: u8 = 0;
    v___x_636_ = l_List_zipIdxLE___redArg(v_le_633_, v_a_634_, v_b_635_);
    return v___x_636_;
}
pub unsafe fn l_List_zipIdxLE___boxed(
    mut v_00_u03b1_637_: *mut crate::leanh::LeanObject,
    mut v_le_638_: *mut crate::leanh::LeanObject,
    mut v_a_639_: *mut crate::leanh::LeanObject,
    mut v_b_640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_641_: u8 = 0;
    let mut v_r_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_641_ = l_List_zipIdxLE(v_00_u03b1_637_, v_le_638_, v_a_639_, v_b_640_);
    v_r_642_ = crate::leanh::lean_box((v_res_641_) as usize);
    return v_r_642_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Sort_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_List_Sort_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_merge___auto__1 = _init_l_List_merge___auto__1();
    crate::leanh::lean_mark_persistent(l_List_merge___auto__1);
    l_List_mergeSort___auto__1 = _init_l_List_mergeSort___auto__1();
    crate::leanh::lean_mark_persistent(l_List_mergeSort___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Sort_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Sort_Basic(builtin);
}
