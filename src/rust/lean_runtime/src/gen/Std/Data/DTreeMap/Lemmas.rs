// Lean compiler output
// Module: Std.Data.DTreeMap.Lemmas
// Imports: Std.Data.DTreeMap.Internal.Lemmas Std.Data.DTreeMap.AdditionalOperations Init.Data.Array.Perm Init.Data.List.Pairwise Init.Data.Prod
use crate::r#gen::Init::Data::Array::Perm::{
    initialize_Init_Data_Array_Perm, runtime_initialize_Init_Data_Array_Perm,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Std::Data::DTreeMap::AdditionalOperations::{
    initialize_Std_Data_DTreeMap_AdditionalOperations,
    runtime_initialize_Std_Data_DTreeMap_AdditionalOperations,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Lemmas::{
    initialize_Std_Data_DTreeMap_Internal_Lemmas,
    runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_utf8_byte_size,
};
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__14_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [99, 111, 109, 112, 97, 114, 101, 0],
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_isSetoid___auto__1___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16710690322389477741 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_isSetoid___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_isSetoid___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_DTreeMap_isSetoid___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_instCoeTypeForall__3(
    mut v_00_u03b1_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_110_ = crate::leanh::lean_box(0);
    return v___x_110_;
}
pub unsafe fn l_Std_DTreeMap_Equiv_instTrans(
    mut v_00_u03b1_111_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_112_: *mut crate::leanh::LeanObject,
    mut v_cmp_113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_114_ = crate::leanh::lean_box(0);
    return v___x_114_;
}
pub unsafe fn l_Std_DTreeMap_Equiv_instTrans___boxed(
    mut v_00_u03b1_115_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_116_: *mut crate::leanh::LeanObject,
    mut v_cmp_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_DTreeMap_Equiv_instTrans(v_00_u03b1_115_, v_00_u03b2_116_, v_cmp_117_);
    crate::leanh::lean_dec_ref(v_cmp_117_);
    return v_res_118_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter___redArg(
    mut v_x_119_: *mut crate::leanh::LeanObject,
    mut v_h__1_120_: *mut crate::leanh::LeanObject,
    mut v_h__2_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_119_) == 0 {
        let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_120_);
        v___x_122_ = crate::leanh::lean_box(0);
        v___x_123_ = crate::leanh::lean_apply_1(v_h__2_121_, v___x_122_);
        return v___x_123_;
    } else {
        let mut v_val_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_121_);
        v_val_124_ = crate::leanh::lean_ctor_get(v_x_119_, 0);
        crate::leanh::lean_inc(v_val_124_);
        crate::leanh::lean_dec_ref_known(v_x_119_, 1);
        v___x_125_ = crate::leanh::lean_apply_1(v_h__1_120_, v_val_124_);
        return v___x_125_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_126_: *mut crate::leanh::LeanObject,
    mut v_motive_127_: *mut crate::leanh::LeanObject,
    mut v_x_128_: *mut crate::leanh::LeanObject,
    mut v_h__1_129_: *mut crate::leanh::LeanObject,
    mut v_h__2_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_128_) == 0 {
        let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_129_);
        v___x_131_ = crate::leanh::lean_box(0);
        v___x_132_ = crate::leanh::lean_apply_1(v_h__2_130_, v___x_131_);
        return v___x_132_;
    } else {
        let mut v_val_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_130_);
        v_val_133_ = crate::leanh::lean_ctor_get(v_x_128_, 0);
        crate::leanh::lean_inc(v_val_133_);
        crate::leanh::lean_dec_ref_known(v_x_128_, 1);
        v___x_134_ = crate::leanh::lean_apply_1(v_h__1_129_, v_val_133_);
        return v___x_134_;
    }
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_161_ = l_Std_DTreeMap_isSetoid___auto__1___closed__10;
    v___x_162_ = l_Lean_mkAtom(v___x_161_);
    return v___x_162_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_163_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__12_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__12,
    );
    v___x_164_ = l_Std_DTreeMap_isSetoid___auto__1___closed__5;
    v___x_165_ = lean_array_push(v___x_164_, v___x_163_);
    return v___x_165_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_167_ = l_Std_DTreeMap_isSetoid___auto__1___closed__14;
    v___x_168_ = lean_string_utf8_byte_size(v___x_167_);
    return v___x_168_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__16() -> *mut crate::leanh::LeanObject
{
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_169_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__15_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__15,
    );
    v___x_170_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_171_ = l_Std_DTreeMap_isSetoid___auto__1___closed__14;
    v___x_172_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_172_, 0, v___x_171_);
    crate::leanh::lean_ctor_set(v___x_172_, 1, v___x_170_);
    crate::leanh::lean_ctor_set(v___x_172_, 2, v___x_169_);
    return v___x_172_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__18() -> *mut crate::leanh::LeanObject
{
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_175_ = crate::leanh::lean_box(0);
    v___x_176_ = l_Std_DTreeMap_isSetoid___auto__1___closed__17;
    v___x_177_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__16_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__16,
    );
    v___x_178_ = crate::leanh::lean_box(2);
    v___x_179_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_179_, 0, v___x_178_);
    crate::leanh::lean_ctor_set(v___x_179_, 1, v___x_177_);
    crate::leanh::lean_ctor_set(v___x_179_, 2, v___x_176_);
    crate::leanh::lean_ctor_set(v___x_179_, 3, v___x_175_);
    return v___x_179_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__19() -> *mut crate::leanh::LeanObject
{
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_180_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__18_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__18,
    );
    v___x_181_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__13_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__13,
    );
    v___x_182_ = lean_array_push(v___x_181_, v___x_180_);
    return v___x_182_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__20() -> *mut crate::leanh::LeanObject
{
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_183_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__19_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__19,
    );
    v___x_184_ = l_Std_DTreeMap_isSetoid___auto__1___closed__11;
    v___x_185_ = crate::leanh::lean_box(2);
    v___x_186_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_186_, 0, v___x_185_);
    crate::leanh::lean_ctor_set(v___x_186_, 1, v___x_184_);
    crate::leanh::lean_ctor_set(v___x_186_, 2, v___x_183_);
    return v___x_186_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__21() -> *mut crate::leanh::LeanObject
{
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_187_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__20_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__20,
    );
    v___x_188_ = l_Std_DTreeMap_isSetoid___auto__1___closed__5;
    v___x_189_ = lean_array_push(v___x_188_, v___x_187_);
    return v___x_189_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__22() -> *mut crate::leanh::LeanObject
{
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__21_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__21,
    );
    v___x_191_ = l_Std_DTreeMap_isSetoid___auto__1___closed__9;
    v___x_192_ = crate::leanh::lean_box(2);
    v___x_193_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_193_, 0, v___x_192_);
    crate::leanh::lean_ctor_set(v___x_193_, 1, v___x_191_);
    crate::leanh::lean_ctor_set(v___x_193_, 2, v___x_190_);
    return v___x_193_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__23() -> *mut crate::leanh::LeanObject
{
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_194_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__22_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__22,
    );
    v___x_195_ = l_Std_DTreeMap_isSetoid___auto__1___closed__5;
    v___x_196_ = lean_array_push(v___x_195_, v___x_194_);
    return v___x_196_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__24() -> *mut crate::leanh::LeanObject
{
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__23_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__23,
    );
    v___x_198_ = l_Std_DTreeMap_isSetoid___auto__1___closed__7;
    v___x_199_ = crate::leanh::lean_box(2);
    v___x_200_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_200_, 0, v___x_199_);
    crate::leanh::lean_ctor_set(v___x_200_, 1, v___x_198_);
    crate::leanh::lean_ctor_set(v___x_200_, 2, v___x_197_);
    return v___x_200_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__25() -> *mut crate::leanh::LeanObject
{
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_201_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__24_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__24,
    );
    v___x_202_ = l_Std_DTreeMap_isSetoid___auto__1___closed__5;
    v___x_203_ = lean_array_push(v___x_202_, v___x_201_);
    return v___x_203_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1___closed__26() -> *mut crate::leanh::LeanObject
{
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_204_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__25_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__25,
    );
    v___x_205_ = l_Std_DTreeMap_isSetoid___auto__1___closed__4;
    v___x_206_ = crate::leanh::lean_box(2);
    v___x_207_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_207_, 0, v___x_206_);
    crate::leanh::lean_ctor_set(v___x_207_, 1, v___x_205_);
    crate::leanh::lean_ctor_set(v___x_207_, 2, v___x_204_);
    return v___x_207_;
}
pub unsafe fn _init_l_Std_DTreeMap_isSetoid___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap_isSetoid___auto__1___closed__26_once),
        _init_l_Std_DTreeMap_isSetoid___auto__1___closed__26,
    );
    return v___x_208_;
}
pub unsafe fn l_Std_DTreeMap_isSetoid(
    mut v_00_u03b1_209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_210_: *mut crate::leanh::LeanObject,
    mut v_cmp_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_212_ = crate::leanh::lean_box(0);
    return v___x_212_;
}
pub unsafe fn l_Std_DTreeMap_isSetoid___boxed(
    mut v_00_u03b1_213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_214_: *mut crate::leanh::LeanObject,
    mut v_cmp_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Std_DTreeMap_isSetoid(v_00_u03b1_213_, v_00_u03b2_214_, v_cmp_215_);
    crate::leanh::lean_dec_ref(v_cmp_215_);
    return v_res_216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_DTreeMap_isSetoid___auto__1 = _init_l_Std_DTreeMap_isSetoid___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap_isSetoid___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Lemmas(builtin);
}
